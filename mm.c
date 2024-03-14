/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Xinyue Li",
    /* First member's email address */
    "lrel7@mail.ustc.edu.cn",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int*)(p))
#define PUT(p, val) (*(unsigned int*)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char*)(bp)-WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char*)(bp)-GET_SIZE(((char*)(bp)-DSIZE)))

static char* heap_listp;  // always points to the prologue block's foot

static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void* find_fit(size_t asize);
static void place(void* bp, size_t asize);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    /*  Create the initial empty heap with 4 words*/
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void*)-1) {
        return -1;
    }

    PUT(heap_listp, 0);                           // the 1st word: padding
    PUT(heap_listp + WSIZE, PACK(DSIZE, 1));      // the 2nd word: prologue header
    PUT(heap_listp + 2 * WSIZE, PACK(DSIZE, 1));  // the 3rd word: prologue footer
    PUT(heap_listp + 3 * WSIZE, PACK(DSIZE, 1));  // the 4th word: epilogue header
    heap_listp += (2 * WSIZE);                    // move `heap_listp` to the prologue block's foot

    /* Extend the empty heap with a free block of `CHUNKSIZE` bytes */
    if (!extend_heap(CHUNKSIZE / WSIZE)) {
        return -1;
    }

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void* mm_malloc(size_t size) {
    size_t asize;  // adjusted block size
    size_t esize;  // amount to extend heap if no fit
    char* bp;

    /* Ignore empty requests */
    if (size == 0) {
        return NULL;
    }

    /* Adjust block size to include overhead and alingment paddings */
    asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if (bp = find_fit(asize)) {
        place(bp, asize);
        return bp;
    }

    /* No fit found, extend the heap and place the block */
    esize = MAX(asize, CHUNKSIZE);
    if (bp = extend_heap(esize / WSIZE)) {
        place(bp, asize);
        return bp;
    }

    /* Malloc failed*/
    return NULL;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void* ptr) {
    /* Get the size of the block */
    size_t size = GET_SIZE(HDRP(ptr));

    /* Set alloc bit to 0 */
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    /* Coalesce if the previous block was free */
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void* mm_realloc(void* ptr, size_t size) {
    void* new_ptr;

    if (!(new_ptr = mm_malloc(size))) {
        return NULL;
    }

    memcpy(new_ptr, ptr, MIN(size, GET_SIZE(HDRP(ptr))));
    mm_free(ptr);
    return new_ptr;
}

/***************************************************************/
/* Helper functions */
/***************************************************************/

/*
 * extend_heap - Extend the heap by words
 * Return NULL on error, the pointer to the new block on success
 */
static void* extend_heap(size_t words) {
    char* bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void*)-1) {
        return NULL;
    }

    /* Init free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));          // free block header
    PUT(FTRP(bp), PACK(size, 0));          // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  // new epilogue header

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * coalesce - Coalesce the current free block with its previous (if free) and/or next (if free) neighbors
 * Return the possibly coalesced block
 */
static void* coalesce(void* bp) {
    /* Get alloc bit of the previous and next block */
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    /* Get size of the current block */
    size_t size = GET_SIZE(HDRP(bp));

    /* Case 1: both the previous and next block are allocated */
    if (prev_alloc && next_alloc) {
        return bp;
    }

    /* Case 2: the previous block is free and the next block is allocated */
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  // get size of the next block
        PUT(HDRP(bp), PACK(size, 0));           // set size of the coalesced block (head)
        PUT(FTRP(bp), PACK(size, 0));           // set size of the coalesced block (foot)
    }

    /* Case 3: the previous block is allocated and the next block is free */
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));  // get size of the previous block
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    /* Case 4: both the previous and next block are free */
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}

/*
 * find_fit - Find the first fit block
 */
static void* find_fit(size_t asize) {
    void* bp;

    /* Go through the heap list*/
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp))) > asize) {  // free and large enough
            return bp;
        }
    }

    /* No fit */
    return NULL;
}

/*
 * place - Place the required `asize` block in the free block pointed by `bp`
 * Split the free block if needed
 */
static void place(void* bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));  // current size of the block

    if ((csize - asize) >= 2 * DSIZE) {
        PUT(HDRP(bp), PACK(asize, 1));  // set size and alloc bit (1)
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);  // move to the rest part
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}