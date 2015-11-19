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
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
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
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */  
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
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

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

static void *coalesce(void *bp) {
    //TODO
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
    ((fl_node *)bp) -> next = freelist_head;  /* Free block next pointer */
    ((fl_node *)bp) -> prev = NULL;           /* Free block prev pointer */
    PUTWORD(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 

    if (freelist_head) {
        ((fl_node *) freelist_head) -> prev = (fl_node *) bp;
    }

    /* Coalesce if the previous block was free */
    //TODO
    bp = coalesce(bp);
    freelist_head = (fl_node *) bp;

    return bp;
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    if (heap_start) {
        /* Not first time initialization */
        byte *bp = (heap_start + DSIZE);

        size_t heap_size = mem_heapsize();
        //TODO not sure how sbrk works in init, hence this dbg_printf
        dbg_printf("In mm_init, heap_size = %u\n", (unsigned int)heap_size);
        size_t block_size = heap_size - DSIZE;
        PUTWORD(heap_start, 0);                    /* Alignment padding */
        PUTWORD(HDRP(bp), PACK(block_size, 0));    /* Block header */
        freelist_head = (fl_node *) bp;         
        freelist_head -> next = NULL;              /* Free block next pointer */
        freelist_head -> prev = NULL;              /* Free block prev pointer */
        PUTWORD(FTRP(bp), PACK(block_size, 0));    /* Block footer */
        mm_checkheap(__LINE__);
        return 0;
    }

    /* First time initialization */

    /**
     * |....|....|
     * |pad |epi |
     */
    if ((heap_start = mem_sbrk(DSIZE)) == (void *) -1) {
        return -1;
    }
    PUTWORD(heap_start, 0);                             /* Alignment padding */
    PUTWORD(heap_start + (1 * WSIZE), PACK(0, 1));      /* Epilogue header */
    mm_checkheap(__LINE__);

    freelist_head = extend_heap(CHUNKSIZE / WSIZE);

    mm_checkheap(__LINE__);
    return 0;
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));   

    if ((csize - asize) >= MIN_BLOCKSIZE) { 
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));

    }
    else { 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * malloc
 */
void *malloc (size_t size) {

    return NULL;
}

/*
 * free
 */
void free (void *ptr) {
    if(!ptr) return;
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

inline void checkheap_printf(int lineno, const char *message) {
    printf("line %d: %s\n", lineno, message);
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

        verbose_printf("epilog block header addr is %llx, value is %d\n",
                (dword)(((byte *) heap_end) + 1 - WSIZE),
                (GETWORD(((byte *) heap_end) + 1 - WSIZE)));
    }

    /* Check each block */
    byte *bp = ((byte *) heap_start) + DSIZE;

    bool prev_isfree = 0;
    int freeblock_count = 0;
    while (bp < heap_end) {
        word header = GETWORD(HDRP(bp));
        word footer = GETWORD(FTRP(bp));
        verbose_printf("line %d: bp = %llx, header = %d, footer = %d\n",
                lineno, (dword) bp, header, footer);
        /* Check header euqals footer */
        if (header != footer) {
            printf("line %d: header != footer for bp = %llx\n",
                    lineno, (dword) bp);
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
        if (!in_heap(p_node))
            checkheap_printf(lineno, "p_node is not in heap");
        if (!in_heap(old_p_node))
            checkheap_printf(lineno, "old_p_node is not in heap");
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
        printf("line %d: freelist_node_count = %d, freeblock_count = %d\n",
                lineno, freelist_node_count, freeblock_count);
    }
}

