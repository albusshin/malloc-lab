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

#define CHECKHEAPx
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
#define CHUNKSIZE  (1<<7)   /* Extend heap by this amount (bytes) */  
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


//TODO try using macros

/* Pack a size and allocated bit into a word */
static inline word PACK(size_t size, int prev_is_free, int prev_is_8, int alloc) {
    return size | (prev_is_free) << 2 | (prev_is_8) << 1 | (alloc);
}

/*
static inline word PACK(size_t size, int prev_is_8, int alloc) {
    return size | (prev_is_8) << 1 | (alloc);
}
*/

static inline word GET_PREV8(byte* bp) {
    return (GETWORD(HDRP(bp)) & 0x2) >> 1;
}

static inline word GET_PREVFREE(byte* bp) {
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
    return (l16node *) TOPTR(p_l16node -> next);
}

static inline l24node *get_next_l24node(l24node *p_l24node) {
    return (l24node *) TOPTR(p_l24node -> next);
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
static inline void insert_treenode(treenode *p_treenode) {
    dbg_printf("insert_treenode, root=%llx, p_treenode=%llx, size = %u\n",
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

static void *coalesce (void *bp) {
    return bp;
}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words, bool add_to_freelist) {
    //TODO dwords?
    byte *bp;
    size_t size;
    dbg_printf("extend_heap, words= %u, add_to_freelist = %d\n",
            (word) words, add_to_freelist);

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if (size < MIN_BLOCKSIZE) size = MIN_BLOCKSIZE;
    if ((long) (bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    word prev8 = GET_PREV8(bp);
    word prevfree = GET_PREVFREE(bp);
    bool now8 = (size == 8);
    
    /* Initialize free block header/footer and the epilogue header */
    PUTWORD(HDRP(bp), PACK(size, prevfree, prev8, 0));  /* Free block header */
    PUTWORD(FTRP(bp), PACK(size, prevfree, prev8, 0));  /* Free block footer */
    PUTWORD(HDRP(NEXT_BLKP(bp)), PACK(0, 1, now8, 1));  /* New epilogue header */

    if (add_to_freelist) {
        if (size == 8) {
            //dbg_printf("size == 8\n");
            l8node *p_l8node = (l8node *)bp;
            add_to_l8(p_l8node);
        }
        else if (size == 16) {
            //dbg_printf("size == 16\n");
            l16node *p_l16node = (l16node *)bp;
            add_to_l16(p_l16node);
        }
        else if (size == 24) {
            //dbg_printf("size == 24\n");
            l24node *p_l24node = (l24node *)bp;
            add_to_l24(p_l24node);
        }
        else {
            //dbg_printf("size > 24\n");
            treenode *p_treenode = (treenode *)bp;
            p_treenode -> left = 0;
            p_treenode -> mid = 0;
            p_treenode -> right = 0;
            p_treenode -> parent = 0;
            insert_treenode(p_treenode);
        }

        /* Coalesce if the previous block was free */
        //dbg_printf("Before extend_heap coalescing, bp = %llx\n", (dword) bp);
        bp = coalesce(bp);
        //dbg_printf("After extend_heap coalescing, bp = %llx\n", (dword) bp);
    }

    return bp;
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    if ((heap_start = mem_sbrk(DSIZE)) == (void *) -1) {
        return -1;
    }

    l8head = 0;    /* 8 bytes block list head */
    l16head = 0;   /* 16 bytes block list head */
    l24head = 0;   /* 24 bytes block list head */
    root = 0;      /* tree root for >24 bytes blocks */

    PUTWORD(heap_start, PACK(0, 0, 0, 1));        /* Prologue footer, padding */
    PUTWORD(heap_start + (1 * WSIZE), PACK(0, 1, 0, 1));   /* Epilogue header */
    extend_heap(CHUNKSIZE / WSIZE, 1);
    //mm_checkheap(__LINE__);
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
         *        X  X  X X X  X  X
         *                X
         *                X <--- Needs to be returned
         */
        while (ret -> mid) {
            ret = get_mid_treenode(ret);
        }
        /* Detatch block from mid list */
        get_parent_treenode(ret) -> mid = 0;
    }
    else {
        treenode *parent = get_parent_treenode(ret);
        treenode *leftchild = get_left_treenode(ret);
        treenode *rightchild = get_right_treenode(ret);
        /* ret doesn't have mid child, need to reconfigure tree.
         *
         *                X <--- Needs to be returned
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
                if (result_is_left) parent -> left = 0;
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
                if (result_is_left) parent -> left = ret -> right;
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
                if (result_is_left) parent -> left = ret -> left;
                else parent -> right = ret -> left;
                leftchild -> parent = TOOFST(parent);
            }
        }
        else { /* (ret -> left && ret -> right) */
            //TODO balancing?
            //TODO throughput. try O(1)? feasible? Or, evalutate O(n) between two.
            /* Case 4: left and right both not NULL */
            if (!parent) {
                /* ret is root */
                /* Save previous right pointer */
                /*
                root = leftchild;
                root -> parent = 0;
                rightchild -> parent = 0;
                insert_treenode(rightchild);
                */
                root = rightchild;
                root -> parent = 0;
                leftchild -> parent = 0;
                insert_treenode(leftchild);
            }
            else {
                /*
                if (result_is_left) parent -> left = ret -> left;
                else parent -> right = ret -> left;
                leftchild -> parent = TOOFST(parent);
                insert_treenode(rightchild);
                */
                if (result_is_left) parent -> left = ret -> right;
                else parent -> right = ret -> right;
                rightchild -> parent = TOOFST(parent);
                insert_treenode(leftchild);
            }
        }
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
    if ((ret = extend_heap(extendsize / WSIZE, 0)) == NULL)
        return NULL;
    return ret;
}

static void place(void *bp, size_t asize) {
    //TODO deal with prev8
    size_t csize = GET_SIZE(HDRP(bp));   
    word remaining_size = csize - asize;
    word prev8 = GET_PREV8(bp);         /* prev block is 8 bytes */
    word now8 = (asize == 8);           /* now block is 8 bytes */

    if (remaining_size >= MIN_BLOCKSIZE) { 
        /* If remaining block is larger than or equal to minimum block size,
         * split the block into two blocks and allocate the first one */
        /* Allocate current block, and
         * Assign to now block if previous block is 8 bytes */
        word next8 = (remaining_size == 8); /* next block is 8 byts */

        /* previous block must not be free */
        PUTWORD(HDRP(bp), PACK(asize, 0, prev8, 1));

        /* Assign to next block if now block is 8 bytes */
        void *newbp = NEXT_BLKP(bp);
        PUTWORD(HDRP(newbp), PACK(remaining_size, 0, now8, 0));

        void *newbp_next = NEXT_BLKP(newbp);
        if (next8) {
            /* Assign to next next block if remaining block is 8 bytes */
            PUTWORD(HDRP(newbp_next), (GETWORD(HDRP(newbp_next)) | 6));

            /* add newbp to list8 */
            add_to_l8((l8node *) newbp);
        }
        //TODO reordering if statements?
        else if (remaining_size == 16) {
            SET_PREVFREE(newbp_next, 1);
            /* add newbp to list16 */
            add_to_l16((l16node *) newbp);
        }
        else if (remaining_size == 24) {
            SET_PREVFREE(newbp_next, 1);
            /* add newbp to list24 */
            add_to_l24((l24node *) newbp);
        }
        else { /* remaining_size > 24 */
            SET_PREVFREE(newbp_next, 1);
            /* add newbp to tree */
            treenode *p_treenode = (treenode *) newbp;
            p_treenode -> left = 0;
            p_treenode -> mid = 0;
            p_treenode -> right = 0;
            p_treenode -> parent = 0;
            insert_treenode(p_treenode);
        }
    }
    else { 
        /* If remaining block is smaller than minimum block size,
         * allocate the whole block */
        /* Allocate current block */
        PUTWORD(HDRP(bp), PACK(csize, 0, prev8, 1));
    }
}

/*
 * malloc
 */
void *malloc (size_t size) {
    //mm_checkheap(__LINE__);
    dbg_printf("malloc, size = %u\n", (word)size);
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
    return NULL;
}

/*
 * free
 */
void free (void *bp) {
    if(!bp) return;
    size_t size = GET_SIZE(HDRP(bp));
    /* Put new boundary tags around the block to free */
    SET_ALLOC(bp, 0);
    if (size > 8) {
        PUTWORD(FTRP(bp), GETWORD(HDRP(bp)));
    }
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
        l8p = get_next_l8node(l8p);
    }
    return count;
}

static inline int get_l16_size() {
    l16node *l16p = l16head;
    int count = 0;
    while (l16p) {
        count++;
        l16p = get_next_l16node(l16p);
    }
    return count;
}

static inline int get_l24_size() {
    l24node *l24p = l24head;
    int count = 0;
    while (l24p) {
        count++;
        l24p = get_next_l24node(l24p);
    }
    return count;
}

static int get_tree_size(treenode *root) {
    if (!root) return 0;
    else if (root->left == 0 && root->mid == 0 && root->right == 0) {
        return 1;
    }
    else return 1 + get_tree_size(get_left_treenode(root))
        + get_tree_size(get_mid_treenode(root))
        + get_tree_size(get_right_treenode(root));
}
    
/*
 * mm_checkheap
 */
void mm_checkheap(int lineno) {
    /* Check heap_start */
    if (mem_heap_lo() != heap_start) {
        checkheap_printf(lineno, "mem_heap_lo() != heap_start\n");
    }

    /* Check epilogue block */
    byte *heap_end = mem_heap_hi();
    verbose_printf("heap_start = %llx, heap_end = %llx\n",
            (dword) heap_start, (dword) heap_end);

    if (GET_SIZE(((byte *) heap_end) + 1 - WSIZE)) {
        checkheap_printf(lineno, "epilogue block header size is not 0\n");

        cprintf("epilog block header addr is %llx, value is %d\n",
                (dword)(((byte *) heap_end) + 1 - WSIZE),
                (GETWORD(((byte *) heap_end) + 1 - WSIZE)));
    }

    /* Check each block */
    byte *bp = ((byte *) heap_start) + DSIZE;
    //bool prev_isfree = 0;
    int freeblock_count = 0;

    while (bp && bp < heap_end - 1) {
        word header = GETWORD(HDRP(bp));
        if (GET_SIZE(HDRP(bp)) != 8) {
            word footer = GETWORD(FTRP(bp));
            /* Check header euqals footer */
            if (header != footer) {
                cprintf("line %d: header != footer for bp = %llx, headerp == %llx, footerp == %llx\n",
                        lineno, (dword) bp, (dword) HDRP(bp), (dword)FTRP(bp));
                cprintf("header = %x footer = %x\n", header, footer);
                //TODO debugging.
                exit(-1);
            }
        }
        /* Check block size is smaller than minimum block size */
        if (GET_SIZE(HDRP(bp)) < MIN_BLOCKSIZE) {
            checkheap_printf(lineno, "Header of bp size < MIN_BLOCKSIZE");
        }
        if (GET_ALLOC(HDRP(bp)) == 0) {
            freeblock_count++;
        }
        /* Check coalescing: no two consecutive free blocks in the heap */
        /* TODO supressing.
            if (prev_isfree) {
                checkheap_printf(lineno, "two consecutive free blocks");
            }
            prev_isfree = 1;
        }
        else {
            prev_isfree = 0;
        }
        */

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
    }

}
