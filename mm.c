/*
 * mm.c
 *
 * Tian Xin * txin
 * TODO
 * First, try a explicit free lists approach, with LIFO policy
 * Then, try with Address-ordered policy
 * Then, try with Segregated list, with LIFO poilcy //TODO IMPORTANT
 * Then, try with Seglist with Address-ordered policy,
 * and compare the last two.
 * Then, optimize. 
 * Optimizations always comes last.
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
#define CHUNKSIZE  (1<<8)  /* Extend heap by this amount (bytes) */  
#define MIN_BLOCKSIZE 24    /* Minimum block size for explicit free list */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GETWORD(p)       (*(unsigned int *)(p))            
#define PUTWORD(p, val)  (*(unsigned int *)(p) = (val))    

/* Read and write a dword at address p */
#define GETDWORD(p)      (*(unsigned long long *)(p))            
#define PUTDWORD(p, val) (*(unsigned long long *)(p) = (val))

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


typedef int bool;

/* Assuming 64-bit machines */
typedef unsigned int        word;
typedef unsigned char       byte;
typedef unsigned long long  dword;

//TODO try use macros

typedef struct freelist_node {
    struct freelist_node *next;
    struct freelist_node *prev;
} fl_node;

/*
 * Given a free block pointer bp, return the address of next free block address
 */
inline byte *get_freelist_next(void *bp) {
    return (byte *) *((dword *) bp);
}

/*
 * Given a free block pointer bp, return the address of previous free block address
 */
inline byte *get_freelist_prev(void *bp) {
    return (byte *) *(((dword *) bp) + 1);
}

static fl_node *freelist_head = 0;  /* Head pointer of the free list */

static byte *heap_start = 0;        /* The start of the heap */

static inline void delete_freelist_node (fl_node *p) {
    if (p -> prev) {
        p -> prev -> next = p -> next;
    }
    else {
        freelist_head = p -> next;
    }
    if (p -> next) {
        p -> next -> prev = p -> prev;
    }
}

static void *coalesce (void *bp) {
    word prev_alloc = GET_ALLOC(PREV_FTRP(bp));
    word next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    byte *next_bp = NEXT_BLKP(bp);
    byte *prev_bp = PREV_BLKP(bp);

    fl_node *bp_node = (fl_node *) bp;
    fl_node *bp_next_node = (fl_node *) next_bp;
    fl_node *bp_prev_node = (fl_node *) prev_bp;

    if (prev_alloc && next_alloc) {         /* Case 1 */
        return bp;
    }

    else if (prev_alloc && !next_alloc) {   /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUTWORD(HDRP(bp), PACK(size, 0));
        PUTWORD(FTRP(bp), PACK(size,0));
        /* delete bp_next_node from freelist */
        delete_freelist_node(bp_next_node);
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        //mm_checkheap(__LINE__);
        size += GET_SIZE(HDRP(prev_bp));
        PUTWORD(HDRP(prev_bp), PACK(size, 0));
        PUTWORD(FTRP(prev_bp), PACK(size, 0));
        /* delete bp_node from freelist */

        delete_freelist_node(bp_prev_node);
        bp_prev_node -> next = bp_node -> next;
        bp_prev_node -> prev = bp_node -> prev;
        if (bp_node -> prev) {
            bp_node -> prev -> next = bp_prev_node;
        }
        else {
            freelist_head = bp_prev_node;
        }
        if (bp_node -> next) {
            bp_node -> next -> prev = bp_prev_node;
        }

        bp = prev_bp;
        //mm_checkheap(__LINE__);
        //printf("3.");
    }

    else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(prev_bp)) + GET_SIZE(HDRP(next_bp));
        PUTWORD(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUTWORD(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        delete_freelist_node(bp_prev_node);
        delete_freelist_node(bp_next_node);

        bp_prev_node -> next = bp_node -> next;
        bp_prev_node -> prev = bp_node -> prev;
        if (bp_node -> prev) {
            bp_node -> prev -> next = bp_prev_node;
        }
        else {
            freelist_head = bp_prev_node;
        }
        if (bp_node -> next) {
            bp_node -> next -> prev = bp_prev_node;
        }

        //printf("4.");
        bp = prev_bp;
    }

    return bp;
}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
    byte *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if (size < MIN_BLOCKSIZE) size = MIN_BLOCKSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    PUTWORD(HDRP(bp), PACK(size, 0));         /* Free block header */   
    PUTWORD(FTRP(bp), PACK(size, 0));         /* Free block footer */   
    ((fl_node *) bp) -> next = freelist_head; /* Free block next pointer */
    ((fl_node *) bp) -> prev = NULL;          /* Free block prev pointer */
    PUTWORD(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 

    if (freelist_head) {
        freelist_head -> prev = (fl_node *) bp; /* Next block prev pointer */
    }

    /* Coalesce if the previous block was free */
    dbg_printf("Before extend_heap coalescing, bp = %llx\n", (dword) bp);
    bp = coalesce(bp);
    dbg_printf("After extend_heap coalescing, bp = %llx\n", (dword) bp);
    freelist_head = (fl_node *) bp;

    return bp;
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    dbg_printf("\nmm_init, line %d\n", __LINE__);

    /**
     * |....|....|
     * |pro |epi |
     */
    if ((heap_start = mem_sbrk(DSIZE)) == (void *) -1) {
        return -1;
    }
    PUTWORD(heap_start, PACK(0, 1)); /* Prologue footer, Alignment padding */
    PUTWORD(heap_start + (1 * WSIZE), PACK(0, 1));      /* Epilogue header */
    //mm_checkheap(__LINE__);
    extend_heap(CHUNKSIZE / WSIZE);
    freelist_head -> next = NULL;               /* Free block next pointer */
    freelist_head -> prev = NULL;               /* Free block prev pointer */
    //mm_checkheap(__LINE__);
    return 0;
}

static void *find_fit(size_t asize) {
    fl_node *p_node;
    /* First-fit */
    for (p_node = freelist_head; p_node; p_node = p_node -> next) {
        void *bp = (void *)p_node;
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL; /* No fit */
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
// TODO NEXT.
// First go over design of malloc and free.
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));   
    fl_node *bp_node = (fl_node *) bp;
    if ((csize - asize) >= MIN_BLOCKSIZE) { 
        /* If remaining block is larger than or equal to minimum block size,
         * split the block into two blocks and allocate the first one */
        /* Allocate current block */
        PUTWORD(HDRP(bp), PACK(asize, 1));
        PUTWORD(FTRP(bp), PACK(asize, 1));
        /* Construct freelist */
        void *newbp = NEXT_BLKP(bp);
        fl_node *newbp_node = (fl_node *) newbp;

        /* Assign old prev and next pointers to new freelist node */
        newbp_node -> prev = bp_node -> prev;
        newbp_node -> next = bp_node -> next;
        /* Detatch and assign prev and next pointers for prev and next node */
        if (bp_node -> prev == NULL) {
            freelist_head = newbp_node;
        }
        else {
            bp_node -> prev -> next = newbp_node;
        }
        if (bp_node -> next != NULL) {
            bp_node -> next -> prev = newbp_node;
        }

        /* Construct the boundary tags for the remaining block of memory */
        PUTWORD(HDRP(newbp), PACK(csize-asize, 0));
        PUTWORD(FTRP(newbp), PACK(csize-asize, 0));
    }
    else { 
        /* If remaining block is smaller than minimum block size,
         * allocate the whole block */
        /* Allocate current block */
        PUTWORD(HDRP(bp), PACK(csize, 1));
        PUTWORD(FTRP(bp), PACK(csize, 1));
        if (bp_node -> prev == NULL) {
            freelist_head = bp_node -> next;
        }
        else {
            bp_node -> prev -> next = bp_node -> next;
        }
        if (bp_node -> next != NULL) {
            bp_node -> next -> prev = bp_node -> prev;
        }
    }
}

/*
 * malloc
 */
void *malloc (size_t size) {
    dbg_printf("malloc, size = %u\n", (word)size);
    //mm_checkheap(__LINE__);
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    byte *bp;      
    if (freelist_head == NULL) {
        mm_init();
    }

    /* Ignore spurious requests */
    if (size == 0) {
        return NULL;
    }

    if (size < DSIZE) {
        asize = MIN_BLOCKSIZE + DSIZE;
    }
    else {
        asize = MIN_BLOCKSIZE + ROUNDUP_DIV(size, DSIZE) * DSIZE;
    }
    if ((bp = find_fit(asize)) != NULL) {
        //mm_checkheap(__LINE__);
        place(bp, asize);
        //mm_checkheap(__LINE__);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);                 
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
        return NULL;                                  
    //mm_checkheap(__LINE__);
    place(bp, asize);                                 
    //mm_checkheap(__LINE__);
    return bp;
}

/*
 * free
 */
void free (void *bp) {
    dbg_printf("free, bp = %llx\n", (dword)bp);
    if (bp == 0) return;
    size_t size = GET_SIZE(HDRP(bp));
    //if (freelist_head == 0) {
        //mm_init();
    //}
    /* Put new boundary tags around the block to free */
    PUTWORD(HDRP(bp), PACK(size, 0));
    PUTWORD(FTRP(bp), PACK(size, 0));
    fl_node *bp_node = (fl_node *) bp;
    bp_node -> next = freelist_head;
    bp_node -> prev = NULL;
    if (freelist_head) {
        freelist_head -> prev = bp_node;
    }
    freelist_head = bp_node;

    dbg_printf("Before free coalescing\n");
    coalesce(bp);
    dbg_printf("After free coalescing\n");
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
    if ((GETWORD(((byte *) heap_end) + 1 - WSIZE)) != 1) {
        checkheap_printf(lineno, "epilogue block header is not 1\n");

        printf("epilog block header addr is %llx, value is %d\n",
                (dword)(((byte *) heap_end) + 1 - WSIZE),
                (GETWORD(((byte *) heap_end) + 1 - WSIZE)));
    }

    /* Check each block */
    byte *bp = ((byte *) heap_start) + DSIZE;

    bool prev_isfree = 0;
    int freeblock_count = 0;
    while (bp && bp < heap_end - 1) {
        word header = GETWORD(HDRP(bp));
        word footer = GETWORD(FTRP(bp));
        /* Check header euqals footer */
        //printf("header = %d, footer = %d\n", header, footer);
        if (header != footer) {
            printf("line %d: header != footer for bp = %llx, ",
                    lineno, (dword) bp);
            printf("header = %d, footer = %d\n", header, footer);
        }
        /* Check block size is larger than minimum block size */
        if (GET_SIZE(HDRP(bp)) < MIN_BLOCKSIZE) {
            checkheap_printf(lineno, "Header of bp size < MIN_BLOCKSIZE");
        }
        /* Check coalescing: no two consecutive free blocks in the heap */
        if (GET_ALLOC(HDRP(bp)) == 0) {
            freeblock_count++;
            if (prev_isfree) {
                checkheap_printf(lineno, "two consecutive free blocks");
            }
            prev_isfree = 1;
        }
        else {
            prev_isfree = 0;
        }

        bp += GET_SIZE(HDRP(bp));
    }
    

    /* Check loop in freelist */
    fl_node *hare = freelist_head;
    fl_node *tortoise = freelist_head;
    while (tortoise && hare) {
        tortoise = tortoise -> next;
        hare = hare->next;
        if (!hare) break;
        hare = hare->next;
        if (tortoise == hare) {
            checkheap_printf(lineno, "loop presents in freelist next pointer");
            break;
        }
    }

    /* Check prev is correct */
    fl_node *p_node = freelist_head;
    while (p_node && p_node -> next) {
        fl_node *old_p_node = p_node;
        p_node = p_node -> next;
        if (!in_heap(p_node)) {
            checkheap_printf(lineno, "p_node is not in heap");
        }
        if (!in_heap(old_p_node)) {
            checkheap_printf(lineno, "old_p_node is not in heap");
        }
        if (old_p_node != p_node -> prev) {
            checkheap_printf(lineno, "old_p_node != p_node -> prev");
            break;
        }
    }

    int freelist_node_count = 0;
    /* Check if blocks and free list nodes count match */
    for (p_node = freelist_head; p_node; p_node = p_node -> next) {
        freelist_node_count++;
    }
    if (freelist_node_count != freeblock_count) {
        //printf("line %d: freelist_node_count = %d, freeblock_count = %d\n",
                //lineno, freelist_node_count, freeblock_count);
    }
}

