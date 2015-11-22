/*
 * mm.c - a memory management package
 *
 * Author: Tian Xin * txin
 *
 * This memory management package includes implementations of malloc, calloc,
 * free, realloc functions. It uses segeragated lists together with a binary
 * tree, a header boundary tag in each block, a footer boundary tag in each
 * free block whose size is larger than 8 bytes and several other features.
 *
 * Block structure:
 *      Block size can only be a multiple of 8, and it can vary from 8 to
 *      the maximum possible value.
 *      Each block contains a mandatory 4-byte header, which contains the
 *      following information:
 *      |........ ........ ........ ........|
 *       ^------------------------------^^^^
 *           |                           |||
 *       size of block                   ||`- alloc flag: if the current
 *                                       ||               block is allocated
 *                                       ||
 *                                       |`-- prev8 flag: if the previous
 *                                       |                block is 8 bytes
 *                                       |
 *                                       `--- prevfree flag: if the previous
 *                                                           block is free
 *
 *      The footer of a free block is mandatory, if the block is larger than
 *      8 bytes. The block is aware of the previous block's allocated status,
 *      hence the current block can always know the previous block's size if
 *      it is free: by checking the prev8 tag, or checking the previous block
 *      's footer tag.
 *
 * List structure:
 *      This implementation uses three data structures to store different
 *      sizes of blocks, respectively called list8, list16 and freetree:
 *          1. One singly linked list for blocks with size of 8 bytes (list8)
 *          2. One doubly linked list for blocks with size of 16 bytes (list16)
 *          3. One binary tree for blocks larger than 16 bytes, in which each
 *             root node of a subtree is a head of a doubly linked list, which
 *             contains blocks whose size is the same with this node. This tree
 *             is implemented as a ternary tree, only the mid child of a tree
 *             node can only have mid children, and no left or right ones.
 *             (freetree)
 *      
 *      list8 - the list8_node struct only contains a 4-byte word, which is the
 *          offset of the next node pointer relative to the heap start address.
 *      list16 - the list16_node struct contains two 4-byte words, one is the 
 *          offset of the next node pointer, the other is the offset of the prev
 *          node pointer.
 *      freetree - the treenode struct contains four 4-byte words, respectively
 *          left: the left subtree node pointer offset
 *          right: the right subtree node pointer offset
 *          mid: the mid node pointer offset
 *          parent: the parent node pointer offset
 *
 * malloc implementation:
 *      malloc utilizes the average O(lg(n)) searching time of binary tree and
 *      places the node directly to the block that's been searched for.
 *
 * coalesce implementation:
 *      coalescing uses a O(n) search if a block is present in the list8, and an
 *      O(1) search if a block is present in the list16, and an O(lg(n)) search
 *      if a block is present in the freetree. After finding all the blocks that
 *      needs to be coalesced, these nodes are deleted from their corresponding
 *      data structure and then a bigger block is constructed, and inserted into
 *      the corresponding free list again.
 *
 * free implementation:
 *      free puts new boundary tags around the block to set the block as free,
 *      and adds the free block to the corresponding free list data structure.
 *      Then free does a immediate coalescing for the freed block.
 *
 * calloc implementation:
 *      naive implementation, mallocs and then memset to 0's.
 *
 * realloc implementation:
 *      naive implmenetation, first free the block and then mallocs a new block.
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

#define CHECKHEAP
#ifdef CHECKHEAP
#define cprintf_info(l, m) printf("line %d: %s\n", l, m)
#define cprintf(...) printf(__VA_ARGS__)
#else
#define cprintf_info(l, m)
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
#define CHUNKSIZE  (0x3<<6) /* Extend heap by this amount (bytes) */  
#define MIN_BLOCKSIZE 8     /* Minimum block size this implementation */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/*
 * Pack a size, a prevfree flag ,
 * a prev8 flag and an alloc flag into a word 
 */
#define PACK(s, p, p8, a) ((s) | ((p) << 2) | ((p8) << 1) | (a))

/* Get the prev8 flag for a block pointer */
#define GET_PREV8(bp) ((GETWORD(HDRP(bp)) & 0x2) >> 1)
/* Get the prevfree flag for a block pointer */
#define GET_PREVFREE(bp) ((GETWORD(HDRP(bp)) & 0x4) >> 2)

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

/* Round up division for positive integers */
#define ROUNDUP_DIV(x, y)   ((((x) - 1) / (y)) + 1)

typedef int bool;

/* size types declarations for 64-bit machines */

typedef unsigned char       byte;   /* 1 byte */
typedef unsigned int        word;   /* 4 byte word */
typedef unsigned long long  dword;  /* 8 byte double word */

/* Structure for tree node, for blocks larger than 16 bytes */
typedef struct treenode {
    word left;          /* left child offset */
    word mid;           /* mid child offset */
    word right;         /* right child offset */
    word parent;        /* parent child offset */
} treenode;

/* 8-byte blocks list (list8) node */
typedef struct list8_node {
    word next;          /* next node offset */
} l8node;

/* 16-byte blocks list (list16) node */
typedef struct list16_node {
    word next;          /* next node offset */
    word prev;          /* previous node offset */
} l16node;

static byte        *heap_start = 0;     /* The start of the heap */
static l8node      *l8head = 0;         /* 8 bytes block list (list8) head */
static l16node     *l16head = 0;        /* 16 bytes block list (list16) head */
static treenode    *treeroot = 0;       /* freetree root for blocks >16 bytes */



/******************************************************************************
 *                     Data Structures Helpers Declaration                    *
 ******************************************************************************/

/* SET_PREV8 - set the prev8 flag (see header comment) for the block pointer */
static inline void SET_PREV8(byte *bp, word prev8);

/* SET_PREVFRE - set the prevfree flag (see header comment) for block bp */
static inline void SET_PREVFREE(byte *bp, word prev_is_free);

/* SET_FOOTER - Set a footer for a block pointer bp */
static inline void SET_FOOTER(byte *bp);

/* SET_ALLOC - Set the alloc flag for block pointer bp */
static inline void SET_ALLOC(byte *bp, word alloc);

/* TOPTR - Convert a pointer offset from a word to a true pointer. */
static inline void *TOPTR(word offset);

/* TOOFST - convert a pointer to a word offset relative to the heap start */
static inline word TOOFST(void *ptr);

/* get_next_l8node - get the next node pointer of p_l8node in list8 */
static inline l8node *get_next_l8node(l8node *p_l8node);

/* get_next_l16node - get the next node pointer of p_l16node in list16 */
static inline l16node *get_next_l16node(l16node *p_l16node);

/* get_prev_l16node - get the previous node pointer of p_l16node in list16 */
static inline l16node *get_prev_l16node(l16node *p_l16node);

/* get_left_treenode - get the left child pointer of p_treenode */
static inline treenode *get_left_treenode(treenode *p_treenode);

/* get_mid_treenode - get the middle child pointer of p_treenode */
static inline treenode *get_mid_treenode(treenode *p_treenode);

/* get_right_treenode - get the right child pointer of p_treenode */
static inline treenode *get_right_treenode(treenode *p_treenode);

/* get_parent_treenode - get the parent pointer of p_treenode */
static inline treenode *get_parent_treenode(treenode *p_treenode);

/* add_to_l8 - add p_l8node to list8 */
static inline void add_to_l8(l8node *p_l8node);

/* add_to_l16 - add p_l16node to list16 */
static inline void add_to_l16(l16node *p_l16node);

/* delete_l8node - delete the node p_l8node in list8 */
static void delete_l8node(l8node *p_l8node);

/* delete_l16node - delete the node p_l16node in list16 */
static void delete_l16node(l16node *p_l16node);

/* delete_treenode - delete p_treenode from the freetree */
static inline treenode * delete_treenode(treenode *p_treenode);

/* delete_binary_treenode - 
 *      delete the subtree root p_treenode from the freetree
 */
static void delete_binary_treenode(treenode *p_treenode, bool is_left_child);

/* size_treenode - Get the block size of a tree node */
static inline word size_treenode(treenode *p_treenode);

/* insert_treenode - Insert the treenode pointer into the tree. */
static void insert_treenode(treenode *p_treenode);

/* delete_bp_from_freelist - delete the block pointer bp from its freelist */
static void delete_bp_from_freelist(void *bp, size_t size);

/* add_bp_to_freelist - add the block pointer bp to its freelist */
static void add_bp_to_freelist(void *bp, size_t size);


/******************************************************************************
 *                     Memeory Manager Helpers Declaration                    *
 ******************************************************************************/

/* coalesce - coalesce free blocks around block pointer bp */
static void *coalesce (void *bp);

/* extend_heap - Extend heap with free block and return its block pointer */
static void *extend_heap(size_t dwords);

/*
 * find_best_tree_fit_and_detatch - 
 *      find the best fit in the freetree, and detatch
 *      the found node from freetree. On failure, return NULL.
 */
static void *find_best_tree_fit_and_detatch(size_t asize);

/*
 * find_fit_and_detatch - 
 *      Find the best fit for a request with size asize, and detatch it
 *      from the freelist or freetree. On failure, return NULL
 */
static void *find_fit_and_detatch(size_t asize);

/*
 * place - place the request of size asize to block pointer bp.
 *
 * Assigns every headers necessary, and also
 * checks if the remaining size of a block can be used later
 */
static void place (void *bp, size_t asize); 

/******************************************************************************
 *                         Memeory Managing Package                           *
 ******************************************************************************/

/*
 * mm_init - initializations for this memory managing package
 * return: -1 on error, 0 on success.
 */
int mm_init(void) {
    if ((heap_start = mem_sbrk(DSIZE)) == (void *) -1) {
        return -1;
    }

    l8head = 0;    /* 8 bytes block list head */
    l16head = 0;   /* 16 bytes block list head */
    treeroot = 0;  /* tree root for >16 bytes blocks */

    PUTWORD(heap_start, PACK(0, 0, 0, 1));        /* Prologue footer, padding */
    PUTWORD(heap_start + (1 * WSIZE), PACK(0, 0, 0, 1));   /* Epilogue header */

    /* extend heap for first usage */
    extend_heap(ROUNDUP_DIV(CHUNKSIZE, DSIZE));
    return 0;
}

/*
 * malloc - Allocate a block with at least size bytes of payload 
 */
void *malloc (size_t size) {
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
    }

    /* find fit in heap and place the requested block */
    if ((bp = find_fit_and_detatch(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    return NULL;
}

/*
 * free - Free a block 
 */
void free (void *bp) {
    if(!bp) return;
    size_t size = GET_SIZE(HDRP(bp));

    /* Put new boundary tags around the block to set the block free */
    PUTWORD(HDRP(bp), (GETWORD(HDRP(bp)) & ~1));
    SET_FOOTER(bp);

    add_bp_to_freelist(bp, size);

    /* do immediate coalescing after free a block to reduce fragmentation */
    coalesce(bp);
}

/*
 * realloc - reallocates the block with a new size
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
 * calloc - allocate a block and set the memory inside to zero
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

/******************************************************************************
 *                         Heap Checker and Helpers                           *
 ******************************************************************************/

/*
 * get_l8_size - get the size of list8
 *
 * if VERBOSE mode is on, this function will print the blocks information
 * inside the free list list8
 */
static inline int get_l8_size() {
    l8node *l8p = l8head;
    int count = 0;
    while (l8p) {
        count++;
        verbose_printf("a:%d l8p: bp = %llx, HDRP(l8p) = %u\n",
                GET_ALLOC(HDRP(l8p)), (dword) l8p, GETWORD(HDRP(l8p)));
        l8p = get_next_l8node(l8p);
    }
    return count;
}

/*
 * get_l16_size - get the size of list16
 *
 * if VERBOSE mode is on, this function will print the blocks information
 * inside the free list list16
 */
static inline int get_l16_size() {
    l16node *l16p = l16head;
    int count = 0;
    while (l16p) {
        count++;
        verbose_printf("a:%d l16p: bp = %llx, HDRP(l16p) = %u\n",
                GET_ALLOC(HDRP(l16p)), (dword) l16p, GETWORD(HDRP(l16p)));
        l16p = get_next_l16node(l16p);
    }
    return count;
}

/*
 * get_tree_size - get the size of freetree
 *
 * if VERBOSE mode is on, this function will print the blocks information
 * inside the free tree
 */
static int get_tree_size(treenode *root) {
    if (!root) return 0;
    else if (root->left == 0 && root->mid == 0 && root->right == 0) {
        verbose_printf("a:%d tree: bp = %llx, HDRP(root) = %u\n",
                GET_ALLOC(HDRP(root)), (dword) root, GETWORD(HDRP(root)));
        return 1;
    }
    else {
        verbose_printf("a:%d tree: bp = %llx, HDRP(root) = %u\n",
                GET_ALLOC(HDRP(root)), (dword) root, GETWORD(HDRP(root)));
        return 1 + get_tree_size(get_left_treenode(root))
        + get_tree_size(get_mid_treenode(root))
        + get_tree_size(get_right_treenode(root));
    }
}

size_t g_treenode_size;     /* variable for recursive function inorder_test */

/*
 * inorder_test - test if the tree is in natural order
 *
 * traverse the tree using inorder traversal
 */
static void inorder_test(treenode *root) {
    if (!root) {
        return;
    }
    inorder_test(get_left_treenode(root));
    size_t prev_size = g_treenode_size;
    g_treenode_size = size_treenode(root);
    if (root -> mid) {
        /* Check if the tree list is correct */
        treenode *p = root;
        while ((p = get_mid_treenode(p))) {
            if (size_treenode(p) != size_treenode(root)) {
                cprintf("Tree inconsistent. psize = %u, subtree root size= %u,",
                    (word) size_treenode(p), (word) size_treenode(root));
            }
        }
    }
    if (prev_size >= g_treenode_size) {
        cprintf("Tree inconsistent. prev == %u, now == %u\n",
                (word) prev_size, (word) g_treenode_size);
    }
    inorder_test(get_right_treenode(root));
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

/*
 * check_tree_invariants - check the invariants of the tree
 *
 * This method checks the tree structure and heap constraints recursively.
 * The order of the tree is tested in inorder_test() method
 */
static void check_tree_invariants(int lineno, treenode *root) {
    if (!root) return;
    if (!in_heap(root)) {
        cprintf("line %d: root = %llx, is not in heap \n",
                lineno, (dword)root);
    }
    if (!aligned(root)) {
        cprintf("line %d: root = %llx, is not aligned \n",
                lineno, (dword)root);
    }
    treenode *leftchild = get_left_treenode(root);
    treenode *rightchild = get_right_treenode(root);
    treenode *midchild = get_mid_treenode(root);
    word rootword = TOOFST(root);

    if (leftchild && leftchild -> parent != rootword) {
        cprintf("line %d: parent of leftchild of node %llx is not itself\n",
                lineno, (dword) root);
    }
    if (midchild && midchild -> parent != rootword) {
        cprintf("line %d: parent of midchild of node %llx is not itself\n",
                lineno, (dword) root);
    }
    if (rightchild && rightchild -> parent != rootword) {
        cprintf("line %d: parent of rightchild of node %llx is not itself\n",
                lineno, (dword) root);
    }

    check_tree_invariants(lineno, get_left_treenode(root));
    check_tree_invariants(lineno, get_mid_treenode(root));
    check_tree_invariants(lineno, get_right_treenode(root));
}

/*
 * mm_checkheap - the heap checker.
 *
 * mm_checkheap checks the following invariants:
 *  1. heap_start is in the starting address of the heap
 *  2. epilogue block header size is 0
 *  3. the tree nodes is in natural order 
 *  4. checks each block for the following invariants:
 *      4.0 block invariants:
 *          4.0.1 each block should locate inside the heap
 *          4.0.1 each block pointer should be aligned
 *      4.1 free block whose size is larger than 8 should have
 *          identical header and footer
 *      4.2 for every block with prev8 flags
 *          4.2.1 each block have a previous block of 8 bytes
 *          4.2.2 each block who has a prevfree flag should have a pre-
 *                vious block which is free
 *          4.2.3 each block who doesn't have a prevfree flag should have
 *                a previous block which is allocated
 *      4.3 each block size is smaller than minimum block size
 *      4.4 each block who has a prevfree flag should have a prev-
 *          ious block which is free, vice versa
 *      4.5 no two consecutive free blocks presents in the heap 
 *  5. free blocks count and free list nodes count should match each other
 *  6. nodes in free lists should be in heap
 *  7. nodes in free lists should be aligned
 *  8. nodes pointer offsets in free lists should be consistent
 */
void mm_checkheap(int lineno) {
    /* 1. check if heap_start is in the starting address of the heap */
    if (mem_heap_lo() != heap_start) {
        cprintf_info(lineno, "mem_heap_lo() != heap_start\n");
    }

    /* 2. check epilogue block header size is 0 */
    byte *heap_end = mem_heap_hi();
    if (GET_SIZE(((byte *) heap_end) + 1 - WSIZE)) {
        cprintf_info(lineno, "epilogue block header size is not 0\n");

        cprintf("epilog block header addr is %llx, value is %d\n",
                (dword)(((byte *) heap_end) + 1 - WSIZE),
                (GETWORD(((byte *) heap_end) + 1 - WSIZE)));
    }

    /* 3. check if the tree nodes is in natural order */
    g_treenode_size = 0;
    inorder_test(treeroot);

    /* 4. check each block */
    byte *bp = ((byte *) heap_start) + DSIZE;
    bool prev_isfree = 0;
    int freeblock_count = 0;

    /* for each block until the end of heap  */
    while (bp && bp < heap_end - 1) {
        word header = GETWORD(HDRP(bp));
        byte *bp_end = (bp + GET_SIZE(HDRP(bp))) - 1;

        /* 4.0 check block invariants */
        /* 4.0.1 block is in heap*/
        if (!in_heap(bp)) {
            cprintf("line %d: bp = %llx, is not in heap \n",
                    lineno, (dword)bp);
        }
        if (!in_heap(bp_end)) {
            cprintf("line %d: bp_end = %llx, is not in heap \n",
                    lineno, (dword)bp_end);
        }

        /* 4.0.2 block is aligned 8 bytes */
        if (!aligned(bp)) {
            cprintf("line %d: bp = %llx, is not aligned\n",
                    lineno, (dword)bp);
        }
        if (!aligned(bp_end + 1)) {
            cprintf("line %d: bp_end + 1 = %llx, is not aligned\n",
                    lineno, (dword)(bp_end + 1));
        }

        /* 4.1 check header euqals footer */
        if (GET_SIZE(HDRP(bp)) != 8 && !GET_ALLOC(HDRP(bp))) {
            word footer = GETWORD(FTRP(bp));
            if (header != footer) {
                cprintf("line %d: header != footer for bp = %llx,\
                        headerp == %llx, footerp == %llx\n",
                        lineno, (dword) bp, (dword) HDRP(bp), (dword)FTRP(bp));
                cprintf("header = 0x%x footer = 0x%x\n", header, footer);
            }
        }
        /* 4.2 check block prev8 flag */
        if (GET_PREV8(bp)) {
            /* 4.2.1 check block prev8 flag true */
            if (GET_SIZE(HDRP((byte *)bp - 8))!= 8) {
                cprintf("line %d: prev8 flag is set in bp = %llx,\
                        but prev 8 block bp is not 8 bytes\n",
                        lineno, (dword) bp);
                }
            else {
                /* 
                 * 4.2.2 with prev8 flag and prevfree flag set,
                 * check previous block
                 */
                if (GET_PREVFREE(bp) && GET_ALLOC(HDRP((byte *)bp - 8))) {
                    cprintf("line %d: prev is 8 bytes, prevfree flag is\
                            set but prev block is not free. bp = %llx\n",
                            lineno, (dword) bp);
                }
                /*
                 * 4.2.3 with prev8 flag set and prevfree not set,
                 * check previous block
                 */
                else if (!GET_PREVFREE(bp) &&
                        !GET_ALLOC(HDRP((byte *)bp - 8))) {
                    cprintf("line %d: prev is 8 bytes, prevfree flag is\
                            not set but prev block is free. bp = %llx\n",
                            lineno, (dword) bp);
                }
            }
        }

        /* 4.3 Check block size is smaller than minimum block size */
        if (GET_SIZE(HDRP(bp)) < MIN_BLOCKSIZE) {
            cprintf_info(lineno, "Header of bp size < MIN_BLOCKSIZE");
        }

        /*
         * 4.4 Check consistency between prevfree tag
         * and previous block status 
         */
        if (!GET_PREVFREE(bp) && prev_isfree) {
            cprintf_info(lineno, "prev block is free, but prevfree flag is\
                    not marked");
            cprintf("bp = %llx\n", (dword) bp);
        }
        else if (GET_PREVFREE(bp) && !prev_isfree) {
            cprintf_info(lineno, "prev block is allocated, but prevfree flag\
                    is marked");
            cprintf("bp = %llx\n", (dword) bp);
        }


        if (GET_ALLOC(HDRP(bp)) == 0) {
            verbose_printf("a:%d block: bp = %llx, HDRP(bp) = %u\n",
                    GET_ALLOC(HDRP(bp)), (dword) bp, GETWORD(HDRP(bp)));
            freeblock_count++;
            /* 4.5 check no two consecutive free blocks in the heap */
            if (prev_isfree) {
                cprintf_info(lineno, "two consecutive free blocks,");
                cprintf("bp = %llx\n", (dword) bp);
            }
            prev_isfree = 1;
        }
        else {
            prev_isfree = 0;
        }


        bp += GET_SIZE(HDRP(bp));
    }

    /* 5. check if blocks and free list nodes count match */

    int l8size = get_l8_size();
    int l16size = get_l16_size();
    int treesize = get_tree_size(treeroot);

    int freelist_node_count = l8size + l16size + treesize;
    if (freelist_node_count != freeblock_count) {
        cprintf("line %d: freelist_node_count = %d, freeblock_count = %d\n",
                lineno, freelist_node_count, freeblock_count);
        cprintf("l8 = %d, l16 = %d, tree = %d\n",
                l8size, l16size, treesize);
    }
    /* 6. check nodes in free lists should be in heap */
    /* 7. nodes in free lists should be aligned */
    /* 8. nodes pointer offsets in free lists should be consistent */
    l8node *l8p = l8head;
    l16node *l16p = l16head;
    for (; l8p; l8p = get_next_l8node(l8p)) {
        if (!in_heap(l8p)) {
            cprintf("line %d: l8p = %llx, is not in heap \n",
                    lineno, (dword)l8p);
        }
        if (!aligned(l8p)) {
            cprintf("line %d: l8p = %llx, is not aligned \n",
                    lineno, (dword)l8p);
        }
        /* list8 nodes doesn't have a prev pointer */
    }

    for (; l16p; l16p = get_next_l16node(l16p)) {
        if (!in_heap(l16p)) {
            cprintf("line %d: l16p = %llx, is not in heap \n",
                    lineno, (dword)l16p);
        }
        if (!aligned(l16p)) {
            cprintf("line %d: l16p = %llx, is not aligned \n",
                    lineno, (dword)l16p);
        }
        l16node *prev_node = get_prev_l16node(l16p);
        if (prev_node && (prev_node -> next != TOOFST(l16p))) {
            cprintf("line %d: prev and next inconsistency,",
                    lineno);
            cprintf("l16p = %llx, prev_node = %llx,\
                    prev_node -> next == %u, TOOFST(l16p) == %u",
                    (dword) l16p, (dword) prev_node,
                    prev_node -> next, TOOFST(l16p));
        }
    }

    /* check 6. 7. 8. for the freetree */
    check_tree_invariants(lineno, treeroot);
}

/******************************************************************************
 *                          Memory Manager Helpers                            *
 ******************************************************************************/

/*
 * coalesce - coalesce free blocks around block pointer bp
 *
 * coalesce checks for free blocks in front of and after bp, and coalesces them
 * if necessary. This function uses the current block's header to see previous
 * block's allocated status, and uses the NEXT_BLKP macro to get the next
 * block pointer, and getting its status.
 */
static void *coalesce (void *bp) {
    /* Get next block pointer */
    byte *next_bp = NEXT_BLKP(bp);

    /* From header, read if previous block is allocated using prevfree flag */
    word prev_alloc = !GET_PREVFREE(bp);
    word next_alloc = GET_ALLOC(HDRP(next_bp));

    size_t size = GET_SIZE(HDRP(bp));             /* the current block size */
    size_t next_size = GET_SIZE(HDRP(next_bp));   /* the next block size */

    /* From header, read if previous block is 8 bytes using prev8 flag */
    word prev8 = GET_PREV8(bp);

    if (prev_alloc && next_alloc) {         /* Case 1 */
        /* no need to coalesce */
        return bp;
    }
    else if (prev_alloc && !next_alloc){    /* Case 2 */
        /* coalesce the current block and the next block */
        delete_bp_from_freelist(next_bp, next_size);
        delete_bp_from_freelist(bp, size);

        size += next_size;
        /* prev is not free; prev can be 8 bytes; this block is free*/
        PUTWORD(HDRP(bp), PACK(size, 0, prev8, 0));
        SET_FOOTER(bp);
        add_bp_to_freelist(bp, size);
        
    } else {                                /* !prev_alloc */
        /* previous block is free, initializing previous block information */
        byte *prev_bp;                          /* the previous block pointer */
        size_t prev_size;                       /* the previous block size */
        if (prev8) {
            /* we know the previous block is 8 bytes */
            prev_bp = ((byte *) bp) - 8;
            prev_size = 8;
        }
        else {
            /* get the previous block size using its footer */
            prev_bp = PREV_BLKP(bp);
            prev_size = GET_SIZE(HDRP(prev_bp));
        }
        /* store whether the previous previous block is 8 bytes */
        word prev_prev8 = GET_PREV8(prev_bp);

        if (next_alloc) {                   /* Case 3 */
            /* coalesce the current block with previous block */
            delete_bp_from_freelist(prev_bp, prev_size);
            delete_bp_from_freelist(bp, size);
            size += prev_size;

            /* Previous previous block is not free,
             * Previous block is free*/
            /* assign the header of the new block */
            bp = prev_bp;
            PUTWORD(HDRP(bp), PACK(size, 0, prev_prev8, 0));
            SET_FOOTER(bp);
            add_bp_to_freelist(bp, size);

        }
        else {                              /* Case 4 */
            /* coalesce the previous, current and next block */
            delete_bp_from_freelist(prev_bp, prev_size);
            delete_bp_from_freelist(next_bp, next_size);
            delete_bp_from_freelist(bp, size);
            size += prev_size + next_size;

            /* assign the header of the new block */
            bp = prev_bp;
            PUTWORD(HDRP(bp), PACK(size, 0, prev_prev8, 0));
            SET_FOOTER(bp);
            add_bp_to_freelist(bp, size);
        }
    }
    return bp;
}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t dwords) {
    byte *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = dwords * DSIZE;
    if (size < MIN_BLOCKSIZE) size = MIN_BLOCKSIZE;
    if ((long) (bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    word prev8 = GET_PREV8(bp);
    word prevfree = GET_PREVFREE(bp);

    bool now8 = (size == 8);
    
    /* Initialize free block header/footer and the epilogue header */

    PUTWORD(HDRP(bp), PACK(size, prevfree, prev8, 0)); /* Free block header */
    SET_FOOTER(bp);
    PUTWORD(HDRP(NEXT_BLKP(bp)), PACK(0, 1, now8, 1)); /* New epilogue header */
    add_bp_to_freelist(bp, size);
    /* Coalesce if the previous block was free */
    bp = coalesce(bp);
    return bp;
}

/*
 * find_best_tree_fit_and_detatch - 
 *      find the best fit in the freetree, and detatch
 *      the found node from freetree. On failure, return NULL.
 */
static void *find_best_tree_fit_and_detatch(size_t asize) {
    if (!treeroot) return NULL;     /* return NULL for empty tree */

    treenode *ret = NULL;           /* the return value */
    treenode *nowroot = treeroot;   /* the now root pointer while traversing */
    bool prev_is_left = 0;          /* is nowroot coming from prev -> left */
    bool result_is_left = 1;        /* is ret coming from parent -> left */
    while (nowroot) {
        size_t nowroot_size = size_treenode(nowroot);
        
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
        else {
            /* nowroot not large enough. Try larger blocks */
            nowroot = get_right_treenode(nowroot);
            prev_is_left = 0;
        }
    }
    if (!ret) return NULL;

    /* detatch the treenode from the freetree */
    delete_binary_treenode(ret, result_is_left);
    return ret;
}

/*
 * find_fit_and_detatch - 
 *      Find the best fit for a request with size asize, and detatch it
 *      from the freelist or freetree. On failure, return NULL
 */
static void *find_fit_and_detatch(size_t asize) {
    void *ret = NULL; /* Default: no fit */
    switch (asize) {
    case 8:
        if (l8head) {
            /* For list8, just move l8head ahead one position */
            ret = l8head;
            l8head = get_next_l8node(l8head);
            return ret;
        }
    case 16:
        if (l16head) {
            /* for list16, move l16head ahead one position,
             * and assign the prev of new head to NULL */
            ret = l16head;
            l16head = get_next_l16node(l16head);
            if (l16head) l16head -> prev = 0;
            return ret;
        }
    default:
        /* for other sizes, find the best fit in the freetree */
        ret = find_best_tree_fit_and_detatch(asize);
        if (ret) return ret;
    }
    /* No fit found. Get more memory and place the block */
    size_t extendsize = MAX(asize, CHUNKSIZE);
    if ((ret = extend_heap(ROUNDUP_DIV(extendsize, DSIZE))) == NULL)
        return NULL;
    return find_fit_and_detatch(asize);
}

/*
 * place - place the request of size asize to block pointer bp.
 *
 * Assigns every headers necessary, and also
 * checks if the remaining size of a block can be used later
 */
static void place (void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));   

    word remaining_size = csize - asize;    /* the remaining block size */
    word prev8 = GET_PREV8(bp);             /* if prev block is 8 bytes */
    word now8 = (asize == 8);               /* if now block is 8 bytes */

    if (remaining_size >= MIN_BLOCKSIZE) {
        /* split the block into two blocks and allocate the first one */

        /* previous block can not be free  */
        PUTWORD(HDRP(bp), PACK(asize, 0, prev8, 1));

        /* Assign to next block if now block is 8 bytes */
        void *newbp = NEXT_BLKP(bp);
        PUTWORD(HDRP(newbp), PACK(remaining_size, 0, now8, 0));
        SET_FOOTER(newbp);

        /* cut off the remaining block and add to to freelist */
        add_bp_to_freelist(newbp, remaining_size);
    }
    else { 
        /* allocate the whole block */
        word prevfree = GET_PREVFREE(bp);
        PUTWORD(HDRP(bp), PACK(csize, prevfree, prev8, 1));

        /* Update next block info */
        void *next_bp = NEXT_BLKP(bp);
        SET_PREVFREE(next_bp, 0);
        SET_FOOTER(next_bp);
    }
}

/******************************************************************************
 *                                Helpers                                     *
 ******************************************************************************/

/*
 * SET_PREV8 - set the prev8 flag (see header comment) for the block pointer bp
 */
static inline void SET_PREV8(byte *bp, word prev8) {
    word *hdrp = (word *)HDRP(bp);
    if (prev8) {
        PUTWORD(hdrp, (GETWORD(hdrp) | 0x2));
    }
    else {
        PUTWORD(hdrp, (GETWORD(hdrp) & ~0x2));
    }
}

/*
 * SET_PREVFRE - set the prevfree flag (see header comment) for block bp
 */
static inline void SET_PREVFREE(byte *bp, word prev_is_free) {
    word *hdrp = (word *)HDRP(bp);
    if (prev_is_free) {
        PUTWORD(hdrp, (GETWORD(hdrp) | 0x4));
    }
    else {
        PUTWORD(hdrp, (GETWORD(hdrp) & ~0x4));
    }
}

/*
 * SET_FOOTER - Set a footer for a block pointer bp.
 * set a footer for a block pointer, which is identical as its header.
 * if the block size of *bp is 8, then no footer is set
 * if the block is allocated to the user for usage, no footer is set
 * only those blocks which is lareger than 8 bytes and free has footers.
 */
static inline void SET_FOOTER(byte *bp) {
    if (GET_SIZE(HDRP(bp)) > 8 && !GET_ALLOC(HDRP(bp))) {
        PUTWORD(FTRP(bp), GETWORD(HDRP(bp)));
    }
}

/*
 * SET_ALLOC - Set the alloc flag for block pointer bp
 */
static inline void SET_ALLOC(byte *bp, word alloc){
    word *hdrp = (word *)HDRP(bp);
    if (alloc) {
        PUTWORD(hdrp, (GETWORD(hdrp) | 0x1));
    }
    else {
        PUTWORD(hdrp, (GETWORD(hdrp) & ~0x1));
    }
}

/*
 * TOPTR - Convert a pointer offset from a word to a true pointer.
 */
static inline void *TOPTR(word offset) {
    if (!offset) return NULL;
    return (void*) ((byte *) heap_start + offset);
}

/*
 * TOOFST - convert a pointer to a word offset relative to the heap start addr.
 */
static inline word TOOFST(void *ptr) {
    if (!ptr) return 0;
    return (word) ((dword) ptr - (dword)heap_start);
}

/*
 * get_next_l8node - get the next node pointer of p_l8node in list8
 */
static inline l8node *get_next_l8node(l8node *p_l8node) {
    if (p_l8node -> next == 0) return NULL;
    return (l8node *) (heap_start + (p_l8node -> next));
}

/*
 * get_next_l16node - get the next node pointer of p_l16node in list16
 */
static inline l16node *get_next_l16node(l16node *p_l16node) {
    if (p_l16node -> next == 0) return NULL;
    return (l16node *) TOPTR(p_l16node -> next);
}

/*
 * get_prev_l16node - get the previous node pointer of p_l16node in list16
 */
static inline l16node *get_prev_l16node(l16node *p_l16node) {
    if (p_l16node -> prev == 0) return NULL;
    return (l16node *) TOPTR(p_l16node -> prev);
}

/*
 * get_left_treenode - get the left child pointer of p_treenode
 */
static inline treenode *get_left_treenode(treenode *p_treenode) {
    return (treenode *) TOPTR(p_treenode -> left);
}

/*
 * get_mid_treenode - get the middle child pointer of p_treenode
 */
static inline treenode *get_mid_treenode(treenode *p_treenode) {
    return (treenode *) TOPTR(p_treenode -> mid);
}

/*
 * get_right_treenode - get the right child pointer of p_treenode
 */
static inline treenode *get_right_treenode(treenode *p_treenode) {
    return (treenode *) TOPTR(p_treenode -> right);
}

/*
 * get_parent_treenode - get the parent pointer of p_treenode
 */
static inline treenode *get_parent_treenode(treenode *p_treenode) {
    return (treenode *) TOPTR(p_treenode -> parent);
}

/*
 * add_to_l8 - add p_l8node to list8
 */
static inline void add_to_l8(l8node *p_l8node) {
    /* There's no prev pointers in list8 */
    p_l8node -> next = TOOFST(l8head);
    l8head = p_l8node;
}

/*
 * add_to_l16 - add p_l16node to list16
 */
static inline void add_to_l16(l16node *p_l16node) {
    p_l16node -> next = TOOFST(l16head);
    if (l16head) {
        l16head -> prev = TOOFST(p_l16node);
    }
    p_l16node -> prev = 0;
    l16head = p_l16node;
}

/*
 * delete_l8node - delete the node p_l8node in list8
 *
 * the runtime complexity of this function is O(n),
 * because a block of 8 bytes doesn't have a prev pointer.
 */
static void delete_l8node(l8node *p_l8node) {
    if (p_l8node == l8head) l8head = get_next_l8node(l8head);
    else {
        l8node *p = l8head;
        l8node *pnext = NULL;
        while (p && (pnext = TOPTR(p -> next)) != p_l8node) {
            p = pnext;
        }
        p -> next = p_l8node -> next;
    }
}

/*
 * delete_l16node - delete the node p_l16node in list16
 */
static void delete_l16node(l16node *p_l16node) {
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

/*
 * delete_treenode - delete p_treenode from the freetree
 */
static inline treenode * delete_treenode(treenode *p_treenode) {
    treenode *parent = get_parent_treenode(p_treenode);

    if (parent && (TOOFST(p_treenode) == parent -> mid)) {
        /* p_treenode is mid child of parent, update list pointers. */
        parent -> mid = p_treenode -> mid;
        if (p_treenode -> mid) {
            get_mid_treenode(p_treenode) -> parent = p_treenode -> parent;
        }
    }
    else {
        bool is_left_child = 0;
        if (parent)
            is_left_child = (TOOFST(p_treenode) == parent -> left);
        delete_binary_treenode(p_treenode, is_left_child);
    }
    return p_treenode;
}

/*
 * delete_binary_treenode - delete the subtree root p_treenode from the freetree
 */
static void delete_binary_treenode(treenode *p_treenode, bool is_left_child) {
    treenode *parent = get_parent_treenode(p_treenode);
    treenode *leftchild = get_left_treenode(p_treenode);
    treenode *rightchild = get_right_treenode(p_treenode);
    treenode *midchild = get_mid_treenode(p_treenode);

    if (p_treenode -> mid) {
        /* Updating the parent information */
        if (!parent) {
            treeroot = midchild;
            treeroot -> parent = 0;
        }
        else {
            if (is_left_child) parent -> left = p_treenode -> mid;
            else parent -> right = p_treenode -> mid;
            midchild -> parent = p_treenode -> parent;
            
        }
        /* Updating its children */
        midchild -> left = p_treenode -> left;
        midchild -> right = p_treenode -> right;
        if (leftchild) leftchild -> parent = p_treenode -> mid;
        if (rightchild) rightchild -> parent = p_treenode -> mid;
    }
    else {
        /* p_treenode doesn't have mid child, need to reconfigure tree. */
        if (!p_treenode -> left && !p_treenode -> right) {
            /* Case 1: left and right child of nowroot both NULL, hence leaf */
            if (!parent) {
                treeroot = NULL;
            }
            else {
                if (is_left_child) parent -> left = 0;
                else parent -> right = 0;
            }
        }
        else if (!p_treenode -> left && p_treenode -> right) {
            /* Case 2: left is NULL and right is not NULL */
            if (!parent) {
                /* p_treenode is treeroot */
                treeroot = rightchild;
                treeroot -> parent = 0;
            }
            else {
                if (is_left_child) parent -> left = p_treenode -> right;
                else parent -> right = p_treenode -> right;
                rightchild -> parent = TOOFST(parent);
            }
        }
        else if (p_treenode -> left && !p_treenode -> right) {
            /* Case 3: left is not NULL and right is NULL */
            if (!parent) {
                /* p_treenode is treeroot*/
                treeroot = leftchild;
                treeroot -> parent = 0;
            }
            else {
                if (is_left_child) parent -> left = p_treenode -> left;
                else parent -> right = p_treenode -> left;
                leftchild -> parent = TOOFST(parent);
            }
        }
        else { /* (p_treenode -> left && p_treenode -> right)
                *
                *                X <--- Needs to be deleted
                *           X         X
                *        X  X  X   X  X  X
                *                  ^
                *                  |
                *                  The node to replace p_treenode 
                */
            /* Get the smallest node on the right subtree */
            treenode *rightleast = get_right_treenode(p_treenode);
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
                rightleast -> left = p_treenode -> left;
                rightleast -> right = p_treenode -> right;
                if (p_treenode -> left) {
                    leftchild -> parent = TOOFST(rightleast);
                }
                if (p_treenode -> right) {
                    rightchild -> parent = TOOFST(rightleast);
                }

                /* And replace the p_treenode's position with this one */
                if (!parent) {
                    treeroot = rightleast;
                    treeroot -> parent = 0;
                }

                else {
                    if (is_left_child) parent -> left = TOOFST(rightleast);
                    else parent -> right = TOOFST(rightleast);
                    rightleast -> parent = p_treenode -> parent;
                }
            }
            else {
                /* rightleast is the first right child of p_treenode */
                if (!parent) {
                    treeroot = rightleast;
                    treeroot -> parent = 0;
                    treeroot -> left = p_treenode -> left;
                    leftchild -> parent = p_treenode -> right;
                }
                else {
                    if (is_left_child) parent -> left = p_treenode -> right;
                    else parent -> right = p_treenode -> right;
                    rightleast -> parent = p_treenode -> parent;
                    rightleast -> left = p_treenode -> left;
                    leftchild -> parent = p_treenode -> right;
                }
            }
        }
    }
}

/*
 * size_treenode - Get the block size of a tree node
 */
static inline word size_treenode(treenode *p_treenode) {
    return GET_SIZE(HDRP(p_treenode));
}

/*
 * insert_treenode - insert the treenode pointer into the freetree.
 * If the treenode root doesn't exist, the new node becomes the root.
 */
static void insert_treenode(treenode *p_treenode) {
    if (!treeroot) {
        treeroot = p_treenode;
        p_treenode -> parent = 0;
        return;
    }
    word node_size = size_treenode(p_treenode);
    word rootword = TOOFST(treeroot);
    word p_treenodeword = TOOFST(p_treenode);
    /* pointer to the offset inside a treenode */
    word *rover = &rootword;
    treenode *parent = 0;
    while (*rover) {
        treenode *p_rover = (treenode *) TOPTR(*rover);
        word rover_size = size_treenode(p_rover);
        /* If an exact match is found, replace the head of the midlist */
        if (node_size == rover_size) {
            treenode *roverleft = get_left_treenode(p_rover);
            treenode *roverright = get_right_treenode(p_rover);
            p_treenode -> left = p_rover -> left;
            p_treenode -> right = p_rover -> right;
            if (p_rover -> left) roverleft -> parent = p_treenodeword;
            if (p_rover -> right) roverright -> parent = p_treenodeword;
            p_rover -> left = 0;
            p_rover -> right = 0;
            p_treenode -> mid = *rover;
            p_rover -> parent = p_treenodeword;
            if (!parent) {
                /* p_rover doesn't have parent, update treeroot */
                treeroot = p_treenode;
                p_treenode -> parent = 0;
            }
            else {
                if (parent -> left == *rover) parent -> left = p_treenodeword;
                else parent -> right = p_treenodeword;
                p_treenode -> parent = TOOFST(parent);
            }
            return;
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
    *rover = p_treenodeword;
    p_treenode -> parent = TOOFST(parent);
}

/*
 * delete_bp_from_freelist - delete the block pointer bp from its freelist
 */
static void delete_bp_from_freelist(void *bp, size_t size) {
    switch (size) {
        case 8:
            delete_l8node((l8node *) bp);
            break;
        case 16:
            delete_l16node((l16node *) bp);
            break;
        default:
            delete_treenode((treenode *) bp);
            break;
    }
}

/*
 * add_bp_to_freelist - add the block pointer bp to its freelist
 *
 * this function also sets all the necessary headers and footers
 * for the next block, to indicate current block is free and 
 * to indicate if the current block is 8 bytes.
 */
static void add_bp_to_freelist(void *bp, size_t size) {
    /* Put next block's header and possibly footer tag
     * to indicate its prev block is free*/
    void * next_bp = NEXT_BLKP(bp);
    SET_PREV8(next_bp, size == 8);
    SET_PREVFREE(next_bp, 1);
    SET_FOOTER(next_bp);

    treenode *p_treenode = (treenode *)bp;
    switch (size) {
        case 8:
            add_to_l8((l8node *) bp);
            break;
        case 16:
            add_to_l16((l16node *) bp);
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

