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
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

#define CHECKHEAPx
#ifdef CHECKHEAP
#define checkheap_printf(l, m) printf("line %d: %s\n", l, m)
#else
#define checkheap_printf(l, m)
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
#define CHUNKSIZE  (1<<4)   /* Extend heap by this amount (bytes) */  
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
    struct treenode *left;
    struct treenode *mid;
    struct treenode *right;
} treenode;

/* 8-byte blocks list node */
typedef struct list8_node {
    word next_offset;
} l8node;

/* 16-byte blocks list node */
typedef struct list16_node {
    struct list16_node *next;
} l16node;

/* 24-byte blocks list node */
typedef struct list24_node {
    struct list24_node *next;
} l24node;

static byte *heap_start = 0;       /* The start of the heap */
static l8node      *l8head = 0;    /* 8 bytes block list head */
static l16node     *l16head = 0;   /* 16 bytes block list head */
static l24node     *l24head = 0;   /* 24 bytes block list head */
static treenode    *root = 0;      /* tree root for >24 bytes blocks */


//TODO try using macros

/* Pack a size and allocated bit into a word */
static inline word PACK(size_t size, int prev_is_8, int alloc) {
    return size | (prev_is_8) << 1 | (alloc);
}

static inline word GET_PREV8(byte* bp) {
    return GETWORD(HDRP(bp)) & 0x2;
}

static inline l8node *get_next_l8node(l8node *p_l8node) {
    if (p_l8node -> next_offset == 0) return NULL;
    return (l8node *) (heap_start + (p_l8node -> next_offset));
}

static inline word get_l8node_offset(l8node *p) {
    if (!p) return 0;
    return (word) ((dword) p - (dword) heap_start);
}

static inline void add_to_l8(l8node *p_l8node) {
    p_l8node -> next_offset = get_l8node_offset(l8head);
    l8head = p_l8node;
}

static inline void add_to_l16(l16node *p_l16node) {
    p_l16node -> next = l16head;
    l16head = p_l16node;
}

static inline void add_to_l24(l24node *p_l24node) {
    p_l24node -> next = l24head;
    l24head = p_l24node;
}

/*
 * Get the block size of a tree node
 */
static inline word size_tn(treenode *p_treenode) {
    return GET_SIZE(HDRP(p_treenode));
}

/*
 * Given a subtree root and a treenode pointer,
 * append the pointer to the end of the mid list of the subtree root
 */
/*
static inline void append_mid(treenode *root, treenode *p_treenode) {
    treenode *p = root;
    while (p -> mid) {
        p = p -> mid;
    }
    p -> mid = p_treenode;
}
*/

/*
 * Insert the treenode pointer into the tree.
 * If the treenode root doesn't exist, the new node becomes the root.
 */
static inline void insert_treenode(treenode *p_treenode) {
    if (!root) {
        root = p_treenode;
        return;
    }
    word node_size = size_tn(p_treenode);
    treenode **rover = &root;       /* 2 dimensional pointer to update node */
    while (*rover) {
        word rover_size = size_tn(*rover);
        /* If an exact match is found, find the tail of the midlist */
        if (node_size == rover_size) {
            while (*rover) {
                rover = &((*rover) -> mid);
            }
            break;
        }
        /* Go to left if the block size is smaller than rover's block size */
        if (node_size < rover_size) {
            rover = &((*rover) -> left);
        }
        /* Go to right if the block size is larger than rover's block size */
        else {
            rover = &((*rover) -> right);
        }
    }
    /* If we found the value in where rover points to is NULL,
     * just update the value in where rover points to as the new node addr */
    *rover = p_treenode;
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

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if (size < MIN_BLOCKSIZE) size = MIN_BLOCKSIZE;
    if ((long) (bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    bool prev8 = 0;
    if (GET_PREV8(bp)) {
        prev8 = 1;
    }
    bool now8 = (size == 8);
    
    /* Initialize free block header/footer and the epilogue header */
    PUTWORD(HDRP(bp), PACK(size, prev8, 0));         /* Free block header */
    PUTWORD(FTRP(bp), PACK(size, prev8, 0));         /* Free block footer */
    PUTWORD(HDRP(NEXT_BLKP(bp)), PACK(0, now8, 1));  /* New epilogue header */

    if (add_to_freelist) {
        if (size == 8) {
            l8node *p_l8node = (l8node *)bp;
            add_to_l8(p_l8node);
        }
        else if (size == 16) {
            l16node *p_l16node = (l16node *)bp;
            add_to_l16(p_l16node);
        }
        else if (size == 24) {
            l24node *p_l24node = (l24node *)bp;
            add_to_l24(p_l24node);
        }
        else {
            treenode *p_treenode = (treenode *)bp;
            insert_treenode(p_treenode);
        }

        /* Coalesce if the previous block was free */
        dbg_printf("Before extend_heap coalescing, bp = %llx\n", (dword) bp);
        bp = coalesce(bp);
        dbg_printf("After extend_heap coalescing, bp = %llx\n", (dword) bp);
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
    PUTWORD(heap_start, PACK(0, 0, 1)); /* Prologue footer, Alignment padding */
    PUTWORD(heap_start + (1 * WSIZE), PACK(0, 0, 1));      /* Epilogue header */
    extend_heap(CHUNKSIZE / WSIZE, 0);
    return 0;
}

/*
 * Find the best fit in the freetree, and detatch the found node from freetree.
 * On failure, return NULL
 * TODO NEXT
 * Hope you've had a good night's sleep.
 * Don't forget, this is the hardest one, so think straight before you start!
 * You've slept for a clearer mind, so I trust you.
 * And, also, don't forget that you can be one of the greatests!
 */
static void *find_best_tree_fit_and_detatch(size_t asize) {

    return NULL;
}

/*
 * Find the best fit for asize and detatch it from the freelist or freetree.
 * On failure, return NULL
 */
static void *find_fit_and_detatch(size_t asize) {
    void *ret = NULL; /* Default: no fit */
    if (asize == 8) {
        if (l8head) {
            ret = l8head;
            l8head = get_next_l8node(l8head);
            return ret;
        }
        else if (l16head) {
            ret = l16head;
            l16head = l16head -> next;
            return l16head;
        }
        else if (l24head) {
            ret = l24head;
            l24head = l24head -> next;
            return l24head;
        }
        else {
            ret = find_best_tree_fit_and_detatch(asize);
            if (ret) return ret;
        }
    }
    /* No fit found. Get more memory and place the block */
    size_t extendsize = MAX(asize, CHUNKSIZE);
    if ((ret = extend_heap(extendsize / WSIZE, 1)) == NULL)
        return NULL;
    return ret;
}

static void place(void *bp, size_t asize) {
    //TODO deal with prev8
}

/*
 * malloc
 */
void *malloc (size_t size) {
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

    if (size < WSIZE) {
        asize = DSIZE;
    }
    else {
        asize = ROUNDUP_DIV((WSIZE + size), DSIZE) * DSIZE;
    }

    if ((bp = find_fit_and_detatch(asize)) != NULL) {
        //place(bp, asize);
        //return bp;
    }
    return NULL;
}

/*
 * free
 */
void free (void *bp) {
    if(!bp) return;
    size_t size = GET_SIZE(HDRP(bp));
    word prev8 = GET_PREV8(bp);
    /* Put new boundary tags around the block to free */
    PUTWORD(HDRP(bp), PACK(size, prev8, 0));
    if (size > 8) {
        PUTWORD(FTRP(bp), PACK(size, prev8, 0));
    }
    //TODO consider dealing with prev8 tag
    if (size == 8) add_to_l8((l8node *) bp);
    else if (size == 16) add_to_l16((l16node *) bp);
    else if (size == 24) add_to_l24((l24node *) bp);
    else insert_treenode((treenode *) bp);
    coalesce(bp);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    return NULL;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    return NULL;
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
 * mm_checkheap
 */
void mm_checkheap(int lineno) {
}
