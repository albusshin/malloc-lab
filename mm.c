/*
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUGx
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

#define CHECKHEAP
#ifdef CHECKHEAP
#define checkheap_printf(l, m) printf("line %d: %s\n", l, m)
#define cprintf(...) printf(__VA_ARGS__)
#else
#define checkheap_printf(l, m)
#define cprintf(...)
#endif

#define VERBOSEx
#ifdef VERBOSE
# define verbose_printf(...) printf(__VA_ARGS__)
#else
# define verbose_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<9)   /* Extend heap by this amount (bytes) */  
#define MIN_BLOCKSIZE 8     /* Minimum block size this implementation */

#define MAX(x, y) ((x) > (y)? (x) : (y))  
#define MIN(x, y) ((x) < (y)? (x) : (y))  

/* Read and write a word at address p */
#define GETWORD(p)       (*(unsigned int *)(p))            
#define PUTWORD(p, val)  (*(unsigned int *)(p) = (val))    

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GETWORD(p) & ~0x7)                   
#define GET_ALLOC(p) (GETWORD(p) & 0x1)                    


/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((byte *)(bp) - WSIZE)                      
#define FTRP(bp)       ((byte *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((byte *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((byte *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

/* Given block ptr bp, compute address of previous block footer */
#define PREV_FTRP(bp)  ((byte *)(bp) - DSIZE)

/* Round up division for positive integers */
#define ROUNDUP_DIV(x, y)   ((((x) - 1) / (y)) + 1)

#define UINT_MAX 0xFFFFFFFF;



typedef int bool;

/* Assuming 64-bit machines */
typedef unsigned int        word;
typedef unsigned char       byte;
typedef unsigned long long  dword;

/* Structure for tree node, for blocks larger than 24 bytes */
typedef struct treenode {
    word left;
    word mid;
    word right;
    word parent;
} treenode;

/* 8-byte blocks list node */
typedef struct list8_node {
    word next;
} l8node;

/* 16-byte blocks list node */
typedef struct list16_node {
    word next;
    word prev;
} l16node;

//TODO put 24 inside tree?
/* 24-byte blocks list node */
typedef struct list24_node {
    word next;
    word prev;
} l24node;

static byte        *heap_start = 0; /* The start of the heap */
static l8node      *l8head = 0;     /* 8 bytes block list head */
static l16node     *l16head = 0;    /* 16 bytes block list head */
static l24node     *l24head = 0;    /* 24 bytes block list head */
static treenode    *root = 0;       /* tree root for >24 bytes blocks */

static void insert_treenode(treenode *p_treenode);

//TODO try using macros

/* Pack a size and allocated bit into a word */
static inline word 
PACK(size_t size, int prev_is_free, int prev_is_8, int alloc) {
    return size | (prev_is_free) << 2 | (prev_is_8) << 1 | (alloc);
}

/*
static inline word PACK(size_t size, int prev_is_8, int alloc) {
    return size | (prev_is_8) << 1 | (alloc);
}
*/

static inline word GET_PREV8(byte *bp) {
    return (GETWORD(HDRP(bp)) & 0x2) >> 1;
}

static inline void SET_PREV8(byte *bp, word prev8) {
    word *hdrp = (word *)HDRP(bp);
    if (prev8) {
        PUTWORD(hdrp, (GETWORD(hdrp) | 0x2));
    }
    else {
        PUTWORD(hdrp, (GETWORD(hdrp) & ~0x2));
    }
}

static inline word GET_PREVFREE(byte *bp) {
    return (GETWORD(HDRP(bp)) & 0x4) >> 2;
}

static inline void SET_PREVFREE(byte *bp, word prev_is_free) {
    word *hdrp = (word *)HDRP(bp);
    if (prev_is_free) {
        PUTWORD(hdrp, (GETWORD(hdrp) | 0x4));
    }
    else {
        PUTWORD(hdrp, (GETWORD(hdrp) & ~0x4));
    }
}

static inline void SET_FOOTER(byte *bp) {
    if (GET_SIZE(HDRP(bp)) > 8 && !GET_ALLOC(HDRP(bp))) {
        PUTWORD(FTRP(bp), GETWORD(HDRP(bp)));
    }
}

static inline void SET_ALLOC(byte *bp, word alloc){
    word *hdrp = (word *)HDRP(bp);
    if (alloc) {
        PUTWORD(hdrp, (GETWORD(hdrp) | 0x1));
    }
    else {
        PUTWORD(hdrp, (GETWORD(hdrp) & ~0x1));
    }
}

static inline void *TOPTR(word offset) {
    if (!offset) return NULL;
    return (void*) ((byte *) heap_start + offset);
}

static inline word TOOFST(void *ptr) {
    if (!ptr) return 0;
    return (word) ((dword) ptr - (dword)heap_start);
}

static inline l8node *get_next_l8node(l8node *p_l8node) {
    if (p_l8node -> next == 0) return NULL;
    return (l8node *) (heap_start + (p_l8node -> next));
}

static inline l16node *get_next_l16node(l16node *p_l16node) {
    if (p_l16node -> next == 0) return NULL;
    return (l16node *) TOPTR(p_l16node -> next);
}

static inline l16node *get_prev_l16node(l16node *p_l16node) {
    if (p_l16node -> prev == 0) return NULL;
    return (l16node *) TOPTR(p_l16node -> prev);
}

static inline l24node *get_next_l24node(l24node *p_l24node) {
    if (p_l24node -> next == 0) return NULL;
    return (l24node *) TOPTR(p_l24node -> next);
}

static inline l24node *get_prev_l24node(l24node *p_l24node) {
    if (p_l24node -> prev == 0) return NULL;
    return (l24node *) TOPTR(p_l24node -> prev);
}

static inline treenode *get_left_treenode(treenode *p_treenode) {
    return (treenode *) TOPTR(p_treenode -> left);
}

static inline treenode *get_mid_treenode(treenode *p_treenode) {
    return (treenode *) TOPTR(p_treenode -> mid);
}

static inline treenode *get_right_treenode(treenode *p_treenode) {
    return (treenode *) TOPTR(p_treenode -> right);
}

static inline treenode *get_parent_treenode(treenode *p_treenode) {
    return (treenode *) TOPTR(p_treenode -> parent);
}

static inline void add_to_l8(l8node *p_l8node) {
    /* There's no prev pointers in list8 */
    p_l8node -> next = TOOFST(l8head);
    l8head = p_l8node;
}

static inline void add_to_l16(l16node *p_l16node) {
    p_l16node -> next = TOOFST(l16head);
    if (l16head) {
        l16head -> prev = TOOFST(p_l16node);
    }
    p_l16node -> prev = 0;
    l16head = p_l16node;
}

static inline void add_to_l24(l24node *p_l24node) {
    p_l24node -> next = TOOFST(l24head);
    if (l24head) {
        l24head -> prev = TOOFST(p_l24node);
    }
    p_l24node -> prev = 0;
    l24head = p_l24node;
}

static void delete_l8node(l8node *p_l8node) {
    //TODO DEBUGGING
    //if (!l8head) return;
    //else
    dbg_printf("[call]\t delete_l8node, p_l8node == %llx\n", (dword) p_l8node);
        if (p_l8node == l8head) l8head = get_next_l8node(l8head);
    else {
        l8node *p = l8head;
        l8node *pnext = NULL;
        while (p && (pnext = TOPTR(p -> next)) != p_l8node) {
            p = pnext;
        }
    //TODO DEBUGGING
        //if (!p) return;
        p -> next = p_l8node -> next;
    }
}

static void delete_l16node(l16node *p_l16node) {
    dbg_printf("[call]\t delete_l16node, p_l16node == %llx\n", (dword) p_l16node);
    if (p_l16node == l16head) {
        l16head = get_next_l16node(l16head);
        if (l16head) {
            l16head -> prev = 0;
        }
    }
    else {
        get_prev_l16node(p_l16node) -> next = p_l16node -> next;
        if (p_l16node -> next) {
            get_next_l16node(p_l16node) -> prev = p_l16node -> prev;
        }
    }
}

static void delete_l24node(l24node *p_l24node) {
    dbg_printf("[call]\t delete_l24node, p_l24node == %llx\n", (dword) p_l24node);
    if (p_l24node == l24head) {
        l24head = get_next_l24node(l24head);
        if (l24head) {
            l24head -> prev = 0;
        }
    }
    else {
        get_prev_l24node(p_l24node) -> next = p_l24node -> next;
        if (p_l24node -> next) {
            get_next_l24node(p_l24node) -> prev = p_l24node -> prev;
        }
    }
}

static treenode * delete_binary_treenode(treenode *ret, bool is_left_child) {
    dbg_printf("[call]\tdelete_binary_treenode, ret = %llx, is_left_child = %u\n",
            (dword) ret, (word) is_left_child);
    treenode *parent = get_parent_treenode(ret);
    treenode *leftchild = get_left_treenode(ret);
    treenode *rightchild = get_right_treenode(ret);
    treenode *midchild = get_mid_treenode(ret);
    dbg_printf("leftchild == %llx, midchild == %llx, rightchild == %llx, parent == %llx\n",
            (dword) leftchild, (dword) midchild, (dword) rightchild, (dword) parent);

    //TODO note this error.
    if (ret -> mid) {
        /* Updating the parent information */
        if (!parent) {
            root = midchild;
            root -> parent = 0;
        }
        else {
            if (is_left_child) parent -> left = ret -> mid;
            else parent -> right = ret -> mid;
            midchild -> parent = ret -> parent;
            
        }
        /* Updating its children */
        midchild -> left = ret -> left;
        midchild -> right = ret -> right;
        if (leftchild) leftchild -> parent = ret -> mid;
        if (rightchild) rightchild -> parent = ret -> mid;
    }
    else {
        /* ret doesn't have mid child, need to reconfigure tree.
         *
         *                X <--- Needs to be deleted
         *           X         X
         *        X  X  X   X  X  X
         */
        if (!ret -> left && !ret -> right) {
            /* Case 1: left and right child of nowroot both NULL, hence leaf */
            if (!ret -> parent) {
                /* ret is root */
                root = NULL;
            }
            else {
                if (is_left_child) parent -> left = 0;
                else parent -> right = 0;
            }
        }
        else if (!ret -> left && ret -> right) {
            /* Case 2: left is NULL and right is not NULL */
            if (!parent) {
                /* ret is root */
                root = rightchild;
                root -> parent = 0;
            }
            else {
                if (is_left_child) parent -> left = ret -> right;
                else parent -> right = ret -> right;
                rightchild -> parent = TOOFST(parent);
            }
        }
        else if (ret -> left && !ret -> right) {
            /* Case 3: left is not NULL and right is NULL */
            if (!parent) {
                /* ret is root */
                root = leftchild;
                root -> parent = 0;
            }
            else {
                if (is_left_child) parent -> left = ret -> left;
                else parent -> right = ret -> left;
                leftchild -> parent = TOOFST(parent);
            }
        }
        else { /* (ret -> left && ret -> right) */
            /* Get the smallest node on the right subtree */
            treenode *rightleast = get_right_treenode(ret);
            if (rightleast -> left) {
                while (rightleast -> left) {
                    rightleast = get_left_treenode(rightleast);
                }
                treenode *rightleast_parent = get_parent_treenode(rightleast);
                treenode *rightleast_right = get_right_treenode(rightleast);
                rightleast_parent -> left = rightleast -> right;
                if (rightleast -> right) {
                    rightleast_right -> parent = rightleast -> parent;
                }
                rightleast -> left = ret -> left;
                rightleast -> right = ret -> right;
                if (ret -> left) {
                    leftchild -> parent = TOOFST(rightleast);
                }
                if (ret -> right) {
                    rightchild -> parent = TOOFST(rightleast);
                }

                /* And replace the ret's position with this one */
                if (!parent) {
                    root = rightleast;
                    root -> parent = 0;
                }

                else {
                    if (is_left_child) parent -> left = TOOFST(rightleast);
                    else parent -> right = TOOFST(rightleast);
                    rightleast -> parent = ret -> parent;
                }
            }
            else {
                /* rightleast is the first right child of ret */
                if (!parent) {
                    root = rightleast;
                    root -> parent = 0;
                    root -> left = ret -> left;
                    leftchild -> parent = ret -> right;
                }
                else {
                    if (is_left_child) parent -> left = ret -> right;
                    else parent -> right = ret -> right;
                    rightleast -> parent = ret -> parent;
                    rightleast -> left = ret -> left;
                    leftchild -> parent = ret -> right;
                }
            }

//            //TODO balancing?
//            //TODO throughput. try O(1)? feasible? Or, evalutate O(n) between two.
//            /* Case 4: left and right both not NULL */
//            if (!parent) {
//                /*
//                root = leftchild;
//                root -> parent = 0;
//                rightchild -> parent = 0;
//                insert_treenode(rightchild);
//                */
//                root = rightchild;
//                root -> parent = 0;
//                leftchild -> parent = 0;
//                insert_treenode(leftchild);
//            }
//            else {
//                /*
//                if (is_left_child) parent -> left = ret -> left;
//                else parent -> right = ret -> left;
//                leftchild -> parent = TOOFST(parent);
//                insert_treenode(rightchild);
//                */
//                if (is_left_child) parent -> left = ret -> right;
//                else parent -> right = ret -> right;
//                rightchild -> parent = TOOFST(parent);
//                insert_treenode(leftchild);
//            }
        }
    }
    return ret;
}

static treenode * delete_treenode(treenode *ret) {
    dbg_printf("[call]\tdelete_treenode, ret = %llx\n", (dword) ret);
    treenode *parent = get_parent_treenode(ret);
    if (parent && (TOOFST(ret) == parent -> mid)) {
        /* ret is mid child of parent, update list pointers. */
        parent -> mid = ret -> mid;
        if (ret -> mid) {
            get_mid_treenode(ret) -> parent = ret -> parent;
        }
    }
    else {
        bool is_left_child = 0;
        if (parent)
            is_left_child = (TOOFST(ret) == parent -> left);
        ret = delete_binary_treenode(ret, is_left_child);
    }
    return ret;
}

/*
 * Get the block size of a tree node
 */
static inline word size_tn(treenode *p_treenode) {
    return GET_SIZE(HDRP(p_treenode));
}

/*
 * Insert the treenode pointer into the tree.
 * If the treenode root doesn't exist, the new node becomes the root.
 */
static void insert_treenode(treenode *p_treenode) {
    dbg_printf("[call]\tinsert_treenode, root=%llx, p_treenode=%llx, size = %u\n",
            (dword) root, (dword) p_treenode, (word) size_tn(p_treenode));

    if (!root) {
        root = p_treenode;
        p_treenode -> parent = 0;
        return;
    }
    word node_size = size_tn(p_treenode);
    word rootword = TOOFST(root);
    /* pointer to the offset inside a treenode */
    word *rover = &rootword;
    treenode *parent = 0;
    while (*rover) {
        treenode *p_rover = (treenode *) TOPTR(*rover);
        word rover_size = size_tn(p_rover);
        //dbg_printf("rover_size == %u, p_treenode size=%u\n",
                //rover_size, node_size);
        /* If an exact match is found, find the tail of the midlist */
        if (node_size == rover_size) {
            while (*rover) {
                parent = p_rover;
                rover = &(p_rover -> mid);
                p_rover = (treenode *) TOPTR(*rover);
            }
            break;
        }
        /* Go to left if the block size is smaller than rover's block size */
        else if (node_size < rover_size) {
            parent = p_rover;
            rover = &(p_rover -> left);
        }
        /* Go to right if the block size is larger than rover's block size */
        else {
            parent = p_rover;
            rover = &(p_rover -> right);
        }
    }
    /* If we found the value in where rover points to is NULL,
     * just update the value in where rover points to as the new node addr */
    *rover = TOOFST(p_treenode);
    p_treenode -> parent = TOOFST(parent);
}

static inline void * get_prev_bp(byte *bp) {
    if (GET_PREV8(bp)) {
        return (void *) (bp - DSIZE);
    }
    else {
        size_t prev_blksz = GET_SIZE(bp - DSIZE);
        return (void *) (bp - prev_blksz);
    }
}

static void delete_bp_from_freelist(void *bp, size_t size) {
    switch (size) {
        case 8:
            delete_l8node((l8node *) bp);
            break;
        case 16:
            delete_l16node((l16node *) bp);
            break;
        case 24:
            delete_l24node((l24node *) bp);
            break;
        default:
            delete_treenode((treenode *) bp);
            break;
    }
}

static void add_bp_to_freelist(void *bp, size_t size) {
    dbg_printf("[call]\tadd_bp_to_freelist, bp = %llx, size = %u\n", (dword) bp, (word) size);
    treenode *p_treenode = (treenode *)bp;
    switch (size) {
        case 8:
            add_to_l8((l8node *) bp);
            break;
        case 16:
            add_to_l16((l16node *) bp);
            break;
        case 24:
            add_to_l24((l24node *) bp);
            break;
        default:
            p_treenode -> left = 0;
            p_treenode -> mid = 0;
            p_treenode -> right = 0;
            p_treenode -> parent = 0;
            insert_treenode(p_treenode);
            break;
    }
}


static void *coalesce (void *bp) {
    dbg_printf("[call]\tcoalesce, bp = %llx\n", (dword) bp);
    //mm_checkheap(__LINE__);

    byte *next_bp = NEXT_BLKP(bp);
    word prev_alloc = !GET_PREVFREE(bp);
    word next_alloc = GET_ALLOC(HDRP(next_bp));
    size_t size = GET_SIZE(HDRP(bp));
    size_t next_size = GET_SIZE(HDRP(next_bp));
    word prev8 = GET_PREV8(bp);

    dbg_printf("next_bp == %llx, next_size == %u, next_alloc == %u, next_header == %u, next_header_addr = %llx\n",
        (dword) next_bp, (word) next_size, (word) next_alloc, (word)GETWORD(HDRP(next_bp)), (dword)HDRP(next_bp));
    dbg_printf("mem_heap_hi() == %llx\n", (dword) mem_heap_hi());
    if (prev_alloc && next_alloc) {         /* Case 1 */
        dbg_printf("[coalescing]\t 1\n");
        return bp;
    }
    else if (prev_alloc && !next_alloc){    /* Case 2 */
        dbg_printf("[coalescing]\t 2, bp = %llx, next_bp = %llx, size = %u, next_size = %u, header = %u\n",
                (dword)bp, (dword)next_bp, (word)size, (word)next_size, (word)GETWORD(HDRP(bp)));
        delete_bp_from_freelist(next_bp, next_size);
        delete_bp_from_freelist(bp, size);

        size += next_size;
        /* prev is not free; prev can be 8 bytes; this block is free*/
        PUTWORD(HDRP(bp), PACK(size, 0, prev8, 0));
        SET_FOOTER(bp);
        add_bp_to_freelist(bp, size);
        
        /* Tell next block this block is free */
        next_bp = NEXT_BLKP(bp);
        SET_PREV8(next_bp, size == 8);
        SET_PREVFREE(next_bp, 1);
        SET_FOOTER(next_bp);
        dbg_printf("[after coalescing]\t 2, bp = %llx, next_bp = %llx, size = %u, next_size = %u, header = %u\n",
                (dword)bp, (dword)next_bp, (word)size, (word)next_size, (word)GETWORD(HDRP(bp)));
    } else {                                /* !prev_alloc */
        byte *prev_bp;
        size_t prev_size;
        if (prev8) {
            /* 8 byte blocks doesn't have footers */
            prev_bp = ((byte *) bp) - 8;
            prev_size = 8;
        }
        else {
            /* previous free block in other sizes has footers */
            prev_bp = PREV_BLKP(bp);
            prev_size = GET_SIZE(HDRP(prev_bp));
        }
        /* If the previous previous block is 8 bytes */
        word prev_prev8 = GET_PREV8(prev_bp);
        if (next_alloc) {                   /* Case 3 */
            dbg_printf("[coalescing]\t 3, bp = %llx, prev_bp = %llx, size = %u, prev_size = %u, header = %u\n",
                (dword)bp, (dword)prev_bp, (word)size, (word)prev_size, (word)GETWORD(HDRP(bp)));
            delete_bp_from_freelist(prev_bp, prev_size);
            delete_bp_from_freelist(bp, size);
            size += prev_size;

            /* Previous previous block is not free,
             * Previous previous block could be 8 bytes,
             * Previous block is free*/
            PUTWORD(HDRP(prev_bp), PACK(size, 0, prev_prev8, 0));
            SET_FOOTER(prev_bp);
            add_bp_to_freelist(prev_bp, size);
            bp = prev_bp;

            /* Tell next block this block is free */
            next_bp = NEXT_BLKP(bp);
            SET_PREV8(next_bp, size == 8);
            SET_PREVFREE(next_bp, 1);
            SET_FOOTER(next_bp);
            dbg_printf("[after coalescing]\t 3, bp = %llx, prev_bp = %llx, size = %u, prev_size = %u, header = %u\n",
                (dword)bp, (dword)prev_bp, (word)size, (word)prev_size, (word)GETWORD(HDRP(bp)));
        }
        else {                              /* Case 4 */
            dbg_printf("[coalescing]\t 4, bp = %llx, prev_bp = %llx, next_bp = %llx, size = %u, prev_size = %u\n, next_size = %u, header = %u\n",
                (dword)bp, (dword)prev_bp, (dword)next_bp, (word)size, (word)prev_size, (word)next_size, (word)GETWORD(HDRP(bp)));
            delete_bp_from_freelist(prev_bp, prev_size);
            delete_bp_from_freelist(next_bp, next_size);
            delete_bp_from_freelist(bp, size);
            size += prev_size + next_size;

            PUTWORD(HDRP(prev_bp), PACK(size, 0, prev_prev8, 0));
            SET_FOOTER(prev_bp);
            add_bp_to_freelist(prev_bp, size);
            bp = prev_bp;

            /* Tell next block this block is free */
            next_bp = NEXT_BLKP(bp);
            SET_PREV8(next_bp, size == 8);
            SET_PREVFREE(next_bp, 1);
            SET_FOOTER(next_bp);
            dbg_printf("[after coalescing]\t 4, bp = %llx, prev_bp = %llx, next_bp = %llx, size = %u, prev_size = %u\n, next_size = %u, header = %u\n",
                (dword)bp, (dword)prev_bp, (dword)next_bp, (word)size, (word)prev_size, (word)next_size, (word)GETWORD(HDRP(bp)));
        }
    }
    dbg_printf("[return]\tcoalesce, bp = %llx, size = %u\n", (dword) bp, (word)size);
    return bp;
}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) {
    //TODO dwords?
    byte *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 

    dbg_printf("[call]\textend_heap, size = %u\n", //, add_to_freelist = %d\n",
            (word) size);//, add_to_freelist);

    if (size < MIN_BLOCKSIZE) size = MIN_BLOCKSIZE;

    //word *heap_end = (word *)((byte*) mem_heap_hi() + 1);
    dbg_printf("[extend_heap] heap_end = %llx, p_epilogue = %llx, epilogue = %u\n",
            (dword) heap_end, (dword) (heap_end - 1), *(heap_end - 1));
    if ((long) (bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    word prev8 = GET_PREV8(bp);
    word prevfree = GET_PREVFREE(bp);

    bool now8 = (size == 8);
    
    /* Initialize free block header/footer and the epilogue header */

    //if (add_to_freelist) {

    dbg_printf("[extend_heap]\t prev8 = %u, prevfree = %u, now8 = %d, size = %u\n",
            (word) prev8, (word) prevfree, now8, (word) size);
    PUTWORD(HDRP(bp), PACK(size, prevfree, prev8, 0));  /* Free block header */
    SET_FOOTER(bp);
    PUTWORD(HDRP(NEXT_BLKP(bp)), PACK(0, 1, now8, 1));  /* New epilogue header */
    add_bp_to_freelist(bp, size);
    /* Coalesce if the previous block was free */
    dbg_printf("Before extend_heap coalescing, bp = %llx\n", (dword) bp);
    bp = coalesce(bp);
    dbg_printf("After extend_heap coalescing, bp = %llx\n", (dword) bp);
    //}
    //else {
    //    //TODO TODO TODO utilization issue might occur
    //    PUTWORD(HDRP(bp), PACK(size, prevfree, prev8, 1));  /* Free block header */
    //    PUTWORD(FTRP(bp), PACK(size, prevfree, prev8, 1));  /* Free block footer */
    //    PUTWORD(HDRP(NEXT_BLKP(bp)), PACK(0, 0, now8, 1));  /* New epilogue header */
    //}
    //mm_checkheap(__LINE__);
    return bp;
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    dbg_printf("[initializing]\n");
    if ((heap_start = mem_sbrk(DSIZE)) == (void *) -1) {
        return -1;
    }

    l8head = 0;    /* 8 bytes block list head */
    l16head = 0;   /* 16 bytes block list head */
    l24head = 0;   /* 24 bytes block list head */
    root = 0;      /* tree root for >24 bytes blocks */

    PUTWORD(heap_start, PACK(0, 0, 0, 1));        /* Prologue footer, padding */
    PUTWORD(heap_start + (1 * WSIZE), PACK(0, 0, 0, 1));   /* Epilogue header */
    extend_heap(CHUNKSIZE / WSIZE);
    return 0;
}

/*
 * Find the best fit in the freetree, and detatch the found node from freetree.
 * On failure, return NULL
 *               X
 *          X    X    X
 *        X X X  X  X X X
 */
static void *find_best_tree_fit_and_detatch(size_t asize) {
    if (!root) return NULL;     /* if the current tree is empty, return NULL */

    treenode *ret = NULL;       /* the return value */
    treenode *nowroot = root;   /* the now root pointer while traversing */
    bool prev_is_left = 0;      /* is nowroot coming from prev -> left */
    bool result_is_left = 1;    /* is ret coming from parent -> left */
    while (nowroot) {
        size_t nowroot_size = size_tn(nowroot);
        
        if (asize == nowroot_size) {
            /* Found best match */
            result_is_left = prev_is_left;
            ret = nowroot;
            break;
        }
        else if (asize < nowroot_size) {
            /* Next best match, update ret info */
            result_is_left = prev_is_left;
            ret = nowroot;
            nowroot = get_left_treenode(nowroot);
            prev_is_left = 1;
        }
        else { /* (asize > nowroot_size) */
            /* nowroot not large enough. Try larger blocks */
            nowroot = get_right_treenode(nowroot);
            prev_is_left = 0;
        }
    }
    if (!ret) return NULL;

    /* Found match, detatch the child from tree */
    else if (ret -> mid) {
        /* ret has mid child, no need to reconfigure tree.
         *
         *                X
         *           X    X    X
         *         X X X  X  X X X
         *                X
         *                X <--- Needs to be deleted and returned
         */
        treenode *parent = ret;
        ret = get_mid_treenode(ret);
        /* Detatch block from mid list */
        parent -> mid = ret -> mid;
        treenode *ret_mid = get_mid_treenode(ret);
        if (ret_mid) {
            ret_mid -> parent = ret -> parent;
        }
    }
    else {
        ret = delete_binary_treenode(ret, result_is_left);
    }
    return ret;
}

/*
 * Find the best fit for asize and detatch it from the freelist or freetree.
 * On failure, return NULL
 */
static void *find_fit_and_detatch(size_t asize) {
    void *ret = NULL; /* Default: no fit */
    switch (asize) {
    case 8:
        if (l8head) {
            /* For l8, just move head ahead one position, it's detatched */
            ret = l8head;
            l8head = get_next_l8node(l8head);
            return ret;
        }
    case 16:
        if (l16head) {
            /* For l16, move head ahead one position,
             * and assign the prev of new head to NULL, then it's detatched. */
            ret = l16head;
            l16head = get_next_l16node(l16head);
            if (l16head) l16head -> prev = 0;
            return ret;
        }
    case 24:
        if (l24head) {
            /* For l24, move head ahead one position,
             * and assign the prev of new head to NULL, then it's detatched. */
            ret = l24head;
            l24head = get_next_l24node(l24head);
            if (l24head) l24head -> prev = 0;
            return ret;
        }
    default:
        ret = find_best_tree_fit_and_detatch(asize);
        dbg_printf("best tree fit ret == %llx\n", (dword) ret);
        if (ret) return ret;
    }
    /* No fit found. Get more memory and place the block */
    size_t extendsize = MAX(asize, CHUNKSIZE);
    if ((ret = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    return find_fit_and_detatch(asize);
}

static void place (void *bp, size_t asize) {
    dbg_printf("[call]\tplace, bp = %llx, size = %u\n", (dword)bp, (word)asize);
    size_t csize = GET_SIZE(HDRP(bp));   
    word remaining_size = csize - asize;
    word prev8 = GET_PREV8(bp);         /* prev block is 8 bytes */
    word now8 = (asize == 8);           /* now block is 8 bytes */

    if (remaining_size >= MIN_BLOCKSIZE) { 
        /* If remaining block is larger than or equal to minimum block size,
         * split the block into two blocks and allocate the first one */
        /* Allocate current block, and
         * Assign to now block if previous block is 8 bytes */
        word next8 = (remaining_size == 8); /* next block is 8 bytes */

        /* previous block must not be free */
        PUTWORD(HDRP(bp), PACK(asize, 0, prev8, 1));

        /* Assign to next block if now block is 8 bytes */
        void *newbp = NEXT_BLKP(bp);
        PUTWORD(HDRP(newbp), PACK(remaining_size, 0, now8, 0));
        SET_FOOTER(newbp);

        void *newbp_next = NEXT_BLKP(newbp);
        if (next8) {
            /* Assign to next next block if remaining block is 8 bytes */
            SET_PREV8(newbp_next, 1);
            SET_PREVFREE(newbp_next, 1);
            SET_FOOTER(newbp_next);
            /* add newbp to list8 */
            add_to_l8((l8node *) newbp);
        }
        //TODO reordering if statements?
        else if (remaining_size == 16) {
            SET_PREV8(newbp_next, 0);
            SET_PREVFREE(newbp_next, 1);
            SET_FOOTER(newbp_next);
            /* add newbp to list16 */
            add_to_l16((l16node *) newbp);
        }
        else if (remaining_size == 24) {
            SET_PREV8(newbp_next, 0);
            SET_PREVFREE(newbp_next, 1);
            SET_FOOTER(newbp_next);
            /* add newbp to list24 */
            add_to_l24((l24node *) newbp);
        }
        else { /* remaining_size > 24 */
            SET_PREV8(newbp_next, 0);
            SET_PREVFREE(newbp_next, 1);
            SET_FOOTER(newbp_next);
            /* add newbp to tree */
            treenode *p_treenode = (treenode *) newbp;
            p_treenode -> left = 0;
            p_treenode -> mid = 0;
            p_treenode -> right = 0;
            p_treenode -> parent = 0;
            insert_treenode(p_treenode);
        }
        dbg_printf("[return]\tplace, bp = %llx, size = %u\n", (dword)bp, (word)asize);
    }
    else { 
        /* If remaining block is smaller than minimum block size,
         * allocate the whole block */
        /* Allocate current block */
        word prevfree = GET_PREVFREE(bp);
        PUTWORD(HDRP(bp), PACK(csize, prevfree, prev8, 1));

        /* Update next block info */
        void *next_bp = NEXT_BLKP(bp);
        /* Didn't change this block size, does't need to set next block's prev8 flag */
        SET_PREVFREE(next_bp, 0);
        SET_FOOTER(next_bp);
        dbg_printf("[return]\tplace, bp = %llx, size = %u\n", (dword)bp, (word)csize);
    }
}

/*
 * malloc
 */
void *malloc (size_t size) {
    //mm_checkheap(__LINE__);
    dbg_printf("[call]\tmalloc, size = %u\n", (word)size);
    size_t asize;      /* Adjusted block size */
    byte *bp;      
    if (heap_start == 0) {
        mm_init();
    }

    /* Ignore spurious requests */
    if (size == 0) {
        return NULL;
    }

    if (size <= WSIZE) {
        asize = DSIZE;
    }
    else {
        asize = ROUNDUP_DIV((WSIZE + size), DSIZE) * DSIZE;
        //asize = ROUNDUP_DIV(size, DSIZE) * DSIZE + MIN_BLOCKSIZE;
    }

    if ((bp = find_fit_and_detatch(asize)) != NULL) {
        //dbg_printf("bp = find_fit_and_detatch(asize) == %llx\n", (dword) bp);
        dbg_printf("Before place, asize == %u, bp == %llx\n", (word) asize, (dword) bp);
        place(bp, asize);
        dbg_printf("After place, bp == %llx\n", (dword) bp);
        return bp;
    }
    //mm_checkheap(__LINE__);
    return NULL;
}

/*
 * free
 */
void free (void *bp) {
    dbg_printf("[call]\tfree, bp = %llx\n", (dword) bp);
    if(!bp) return;
    size_t size = GET_SIZE(HDRP(bp));
    /* Put new boundary tags around the block to free */
    PUTWORD(HDRP(bp), (GETWORD(HDRP(bp)) & ~1));
    SET_FOOTER(bp);
    /* Put next block's header and possibly footer tag
     * to indicate its prev block is free*/
    void * next_bp = NEXT_BLKP(bp);
    SET_PREVFREE(next_bp, 1);
    SET_FOOTER(next_bp);

    if (size == 8) add_to_l8((l8node *) bp);
    else if (size == 16) add_to_l16((l16node *) bp);
    else if (size == 24) add_to_l24((l24node *) bp);
    else {
        treenode *bp_treenode = (treenode *) bp;
        bp_treenode -> left = 0;
        bp_treenode -> mid = 0;
        bp_treenode -> right = 0;
        bp_treenode -> parent = 0;
        insert_treenode(bp_treenode);
    }
    coalesce(bp);
    //mm_checkheap(__LINE__);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(oldptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return malloc(size);
    }

    /* If prev size was enough, return the old pointer*/
    if (GET_SIZE(HDRP(oldptr)) >= size + DSIZE) {
        return oldptr;
    }

    newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(oldptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
    free(oldptr);

    return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

static inline int get_l8_size() {
    l8node *l8p = l8head;
    int count = 0;
    while (l8p) {
        count++;
        verbose_printf("a:%d l8p: bp = %llx, HDRP(l8p) = %u\n", GET_ALLOC(HDRP(l8p)), (dword) l8p, GETWORD(HDRP(l8p)));
        l8p = get_next_l8node(l8p);
    }
    return count;
}

static inline int get_l16_size() {
    l16node *l16p = l16head;
    int count = 0;
    while (l16p) {
        count++;
        verbose_printf("a:%d l16p: bp = %llx, HDRP(l16p) = %u\n", GET_ALLOC(HDRP(l16p)), (dword) l16p, GETWORD(HDRP(l16p)));
        l16p = get_next_l16node(l16p);
    }
    return count;
}

static inline int get_l24_size() {
    l24node *l24p = l24head;
    int count = 0;
    while (l24p) {
        count++;
        verbose_printf("a:%d l24p: bp = %llx, HDRP(l24p) = %u\n", GET_ALLOC(HDRP(l24p)), (dword) l24p, GETWORD(HDRP(l24p)));
        l24p = get_next_l24node(l24p);
    }
    return count;
}

static int get_tree_size(treenode *root) {
    if (!root) return 0;
    else if (root->left == 0 && root->mid == 0 && root->right == 0) {
        verbose_printf("a:%d tree: bp = %llx, HDRP(root) = %u\n", GET_ALLOC(HDRP(root)), (dword) root, GETWORD(HDRP(root)));
        return 1;
    }
    else {
        verbose_printf("a:%d tree: bp = %llx, HDRP(root) = %u\n", GET_ALLOC(HDRP(root)), (dword) root, GETWORD(HDRP(root)));
        return 1 + get_tree_size(get_left_treenode(root))
        + get_tree_size(get_mid_treenode(root))
        + get_tree_size(get_right_treenode(root));
    }
}

size_t g_treenode_size;
static void inorder_test(treenode *root) {
    if (!root) {
        return;
    }
    inorder_test(get_left_treenode(root));
    size_t prev_size = g_treenode_size;
    g_treenode_size = size_tn(root);
    if (root -> mid) {
        /* Check if the tree list is correct */
        treenode *p = root;
        while ((p = get_mid_treenode(p))) {
            if (size_tn(p) != size_tn(root)) {
                cprintf("Tree inconsistent. psize = %u, subtree root size= %u,",
                    (word) size_tn(p), (word) size_tn(root));
            }
        }
    }
    if (prev_size >= g_treenode_size) {
        cprintf("Tree inconsistent. prev == %u, now == %u\n",
                (word) prev_size, (word) g_treenode_size);
    }
    //verbose_printf("%u, ", (word)g_treenode_size);
    inorder_test(get_right_treenode(root));
}

static void preorder_test(treenode *root) {
    if (!root) {
        return;
    }
    //verbose_printf("%u, ", (word) size_tn(root));
    preorder_test(get_left_treenode(root));
    preorder_test(get_right_treenode(root));
}

/*
 * mm_checkheap
 */
void mm_checkheap(int lineno) {
    printf("\n\n");
    /* Check heap_start */
    if (mem_heap_lo() != heap_start) {
        checkheap_printf(lineno, "mem_heap_lo() != heap_start\n");
    }

    /* Check epilogue block */
    byte *heap_end = mem_heap_hi();

    if (GET_SIZE(((byte *) heap_end) + 1 - WSIZE)) {
        checkheap_printf(lineno, "epilogue block header size is not 0\n");

        cprintf("epilog block header addr is %llx, value is %d\n",
                (dword)(((byte *) heap_end) + 1 - WSIZE),
                (GETWORD(((byte *) heap_end) + 1 - WSIZE)));
    }
    if (GET_PREV8(((byte*) heap_end + 1))) {
        checkheap_printf(lineno, "epilogue block header prev8 is set true.\n");

        cprintf("epilog block header addr is %llx, value is %d\n",
                (dword)(((byte *) heap_end) + 1 - WSIZE),
                (GETWORD(((byte *) heap_end) + 1 - WSIZE)));
    }

    /* Check if the tree is in order */
    g_treenode_size = 0;
    inorder_test(root);
    //verbose_printf("\n");
    preorder_test(root);
    //verbose_printf("\n");

    /* Check each block */
    byte *bp = ((byte *) heap_start) + DSIZE;
    bool prev_isfree = 0;
    int freeblock_count = 0;

    while (bp && bp < heap_end - 1) {
        word header = GETWORD(HDRP(bp));
        if (GET_SIZE(HDRP(bp)) != 8 && !GET_ALLOC(HDRP(bp))) {
            word footer = GETWORD(FTRP(bp));
            /* Check header euqals footer */
            if (header != footer) {
                cprintf("line %d: header != footer for bp = %llx, headerp == %llx, footerp == %llx\n",
                        lineno, (dword) bp, (dword) HDRP(bp), (dword)FTRP(bp));
                cprintf("header = 0x%x footer = 0x%x\n", header, footer);
                //TODO debugging
                //exit(-1);
            }
        }
        /* Check block prev8 is true */
        if (GET_PREV8(bp)) {
            cprintf("prev8\n");
            if (GET_SIZE(HDRP((byte *)bp - 8))!= 8) {
                cprintf("line %d: prev8 flag is set in bp = %llx, but prev 8 block bp is not 8 bytes\n",
                        lineno, (dword) bp);
                }
            else {
                if (GET_PREVFREE(bp) && GET_ALLOC(HDRP((byte *)bp - 8))) {
                    cprintf("line %d: prev is 8 bytes, but prevfree flag is set and prev block is not free. bp = %llx\n",
                            lineno, (dword) bp);
                }
                else if (!GET_PREVFREE(bp) && !GET_ALLOC(HDRP((byte *)bp - 8))) {
                    cprintf("line %d: prev is 8 bytes, but prevfree flag is not set and prev block is free. bp = %llx\n",
                            lineno, (dword) bp);
                }
            }
        }

        /* Check block size is smaller than minimum block size */
        if (GET_SIZE(HDRP(bp)) < MIN_BLOCKSIZE) {
            checkheap_printf(lineno, "Header of bp size < MIN_BLOCKSIZE");
        }

        /* Check consistency between prevfree tag and previous block status */
        if (!GET_PREVFREE(bp) && prev_isfree) {
            checkheap_printf(lineno, "prev block is free, but prevfree flag is not marked");
            cprintf("bp = %llx\n", (dword) bp);
        }

        if (GET_ALLOC(HDRP(bp)) == 0) {
            verbose_printf("a:%d block: bp = %llx, HDRP(bp) = %u\n", GET_ALLOC(HDRP(bp)), (dword) bp, GETWORD(HDRP(bp)));
            freeblock_count++;
            /* Check coalescing: no two consecutive free blocks in the heap */
            if (prev_isfree) {
                checkheap_printf(lineno, "two consecutive free blocks,");
                cprintf("bp = %llx\n", (dword) bp);
            }
            prev_isfree = 1;
        }
        else {
            prev_isfree = 0;
        }


        bp += GET_SIZE(HDRP(bp));
    }

    /* Check if blocks and free list nodes count match */

    int l8size = get_l8_size();
    int l16size = get_l16_size();
    int l24size = get_l24_size();
    int treesize = get_tree_size(root);

    int freelist_node_count = l8size + l16size + l24size + treesize;
    if (freelist_node_count != freeblock_count) {
        cprintf("line %d: freelist_node_count = %d, freeblock_count = %d\n",
                lineno, freelist_node_count, freeblock_count);
        cprintf("l8 = %d, l16 = %d, l24 = %d, tree = %d\n",
                l8size, l16size, l24size, treesize);
        //TODO debugging
        //exit(-1);
    }

}
