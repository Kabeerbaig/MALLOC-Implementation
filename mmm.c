#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <stddef.h>
#include "mm.h"
#include "memlib.h"

team_t team = {
       /* Team */
    "Allocation Assassins",
  /* full name of first member */
    "John Tomas",
    /* login ID of first member */
    "00000000",
    /* full name of second member (if any) */
    "Kabeer Baig",
    /* login ID of second member */
    "906390836"
};

// Basic Constrants and Macros
#define WSIZE 4 // Word and header/footer size in bytes
#define DSIZE 8 // Double word size (bytes) 
#define CHUNKSIZE (1<<12) // Extend heap by this amount (bytes) 
#define MINBLOCKSIZE 16 // The minimum size of the freed block

#define MAX(x, y) ((x) > (y)? (x) : (y))
#define ALIGN(size) (((size) + (DSIZE - 1)) & ~0x7)
// Pack a size and allocated bit into a word 
#define PACK(size, alloc) ((size) | (alloc))
// Read and write a word at address p 
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
// Read the size and allocated fields from address p 
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
// Given block ptr bp, compute address of its header and footer 
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
//Given block ptr bp, compute address of next and previous blocks 
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

extern int mm_init (void);
extern void *mm_malloc (size_t size);
extern void mm_free (void *ptr);
extern void *mm_realloc(void *ptr, size_t size);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
//void *mem_sbrk(int incr);

// private global variables 
//static char *mem_heap; //Points to first byte of heap
//static char *mem_brk; //Points to last byte of heap plus 1
//static char *mem_max_addr; //Max legal head addr plus 1
static char *heap_listp = 0; //Always points to the prolouge block; 8 byte allocated block consisting of only a header and footer

// Before calling mm malloc mm realloc or mm free, the application program
// (i.e., the trace-driven driver program that you will use to evaluate your implementation)
// calls mm init to perform any necessary initializations, such as allocating the initial heap
// area. The return value should be -1 if there was a problem in performing the initialization, 0
// otherwise.
extern int mm_init (void) {
    // Create the initial empty heap
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1) {
        return -1;
    }

    PUT(heap_listp, 0); // Alignment padding 
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); //Prologue header 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); //Prologue footer 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); //Epilogue header 
    heap_listp += (2*WSIZE);
// Extend the empty heap with a free block of CHUNKSIZE bytes 
if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
    return -1;
}

return 0;


}
//mm malloc: The mm malloc routine returns a pointer to an allocated block payload of at
// least size bytes. The entire allocated block should lie within the heap region and should
// not overlap with any other allocated chunk
void *mm_malloc(size_t size) {
size_t asize; /* Adjusted block size */
size_t extendsize; /* Amount to extend heap if no fit */
char *bp;
/* Ignore spurious requests */
if (size == 0) {
    return NULL;
}


/* Adjust block size to include overhead and alignment reqs. */
if (size <= DSIZE) {
asize = 2*DSIZE;
}
else {
asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
}

/* Search the free list for a fit */
if ((bp = find_fit(asize)) != NULL) {
place(bp, asize);
return bp;
}

/* No fit found. Get more memory and place the block */
extendsize = MAX(asize,CHUNKSIZE);
if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
return NULL;
}

place(bp, asize);
return bp;

}
// The mm free routine frees the block pointed to by ptr. It returns nothing. This
// routine is only guaranteed to work when the passed pointer (ptr) was returned by an earlier
// call to mm malloc or mm realloc and has not yet been freed.
extern void mm_free (void *ptr) {
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size,0));
   coalesce(ptr);
}

static void *coalesce(void *bp) {
 size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
 size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
 size_t size = GET_SIZE(HDRP(bp));

 if (prev_alloc && next_alloc) { 
    return bp;
    }

 else if (prev_alloc && !next_alloc) { 
 size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
 PUT(HDRP(bp), PACK(size, 0));
 PUT(FTRP(bp), PACK(size,0));
 }

 else if (!prev_alloc && next_alloc) { 
 size += GET_SIZE(HDRP(PREV_BLKP(bp)));
 PUT(FTRP(bp), PACK(size, 0));
 PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
 bp = PREV_BLKP(bp);
 }

 else { 
 size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
 GET_SIZE(FTRP(NEXT_BLKP(bp)));
 PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
 PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
 bp = PREV_BLKP(bp);
 }
 return bp;
 }
// The mm realloc routine returns a pointer to an allocated region of at least
// size bytes with the following constraints.
// – if ptr is NULL, the call is equivalent to mm malloc(size);
// – if size is equal to zero, the call is equivalent to mm free(ptr);
extern void *mm_realloc(void *ptr, size_t size) {
    // Check and see if the pointer is NULL

    if (ptr == NULL) {
        return mm_malloc(size);
    }
    if (size == 0 ) {
        mm_free(ptr);
        return NULL;
    }


    size_t siz = MAX(ALIGN(size) + DSIZE, MINBLOCKSIZE);
    size_t curr_size = GET_SIZE(HDRP(ptr));

    // If size is equal to the current size 

    if (siz == curr_size ) {
        return ptr;
    }

    // IF size is less than the current size 

    if (siz <= curr_size) {
        if (siz > MINBLOCKSIZE && (curr_size - siz) > MINBLOCKSIZE) {
            PUT(HDRP(ptr), PACK(siz, 1));
            PUT(FTRP(ptr), PACK(siz, 1));
            void *block = NEXT_BLKP(ptr);
            PUT(HDRP(block), PACK(curr_size - siz, 0));
            mm_free(block);
        }
        return ptr;
    }

    // If size is larger than the current_size

    size_t big_size = curr_size;
    void *blockk = NEXT_BLKP(ptr);
    // Check to see if you can combine with the next block if it is free

    if (!GET_ALLOC(HDRP(blockk))) {
        big_size += GET_SIZE(HDRP(blockk));
        if (big_size >= siz) {
            PUT(HDRP(ptr), PACK(big_size, 1));
            PUT(FTRP(ptr), PACK(big_size, 1));
            return ptr;
        }
    }
    // Allocate new block so you can copy data to it
    void *new_block = mm_malloc(size);
        if (new_block == NULL) {
            return NULL;
        }
    // Copy the data over
    memcpy(new_block, ptr, curr_size - DSIZE);
    return new_block;
}

// heap checker 
// check for any invariants or consistency conditions
//print error messages when check fails; use as a debugger
//int mm_check(void);

// memlib.c funtions
// Expands the heap by incr bytes, where incr is a positive
// non-zero integer and returns a generic pointer to the first byte of the newly allocated heap
// area. The semantics are identical to the Unix sbrk function, except that mem sbrk accepts
// only a positive non-zero integer argument, and except that mem sbrk returns NULL on
// failure rather than -1.
// void *mem_sbrk(int incr) {
//     char *old_brk = mem_brk;

// if ( (incr < 0) || ((mem_brk + incr) > mem_max_addr)) {
//     errno = ENOMEM;
//  fprintf(stderr, "ERROR: mem_sbrk failed. Ran out of memory...\n");
// return (void *)-1;
//  }
//  mem_brk += incr;
//  return (void *)old_brk;
// }
// Returns a generic pointer to the first byte in the heap.
//void *mem_heap_lo(void);
//Returns a generic pointer to the last byte in the heap.
//void *mem_heap_hi(void);
//Returns the current size of the heap in bytes.
//size_t mem_heapsize(void); 
//Returns the system’s page size in bytes (4K on Linux systems)
//size_t mem_pagesize(void); 

//Extends the heap with new a new free block
static void *extend_heap(size_t words) {
char *bp;
size_t size;

// Allocate an even number of words to maintain alignment 
 size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
if ((long)(bp = mem_sbrk(size)) == -1)
 return NULL;
//Initialize free block header/footer and the epilogue header 
PUT(HDRP(bp), PACK(size, 0)); //Free block header 
PUT(FTRP(bp), PACK(size, 0)); //Free block footer 
PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // New epilogue header 
 // Coalesce if the previous block was free 
return coalesce(bp);
 }

 //Performs a first fit search 

static void *find_fit(size_t asize) {
    void *ptr;

    // Searches through heap list to find a free block

    for (ptr = heap_listp; GET_SIZE(HDRP(ptr)) > 0; ptr = NEXT_BLKP(ptr)) {

        // Check to see if the current block is not allocated 
        // Also check to see is the size is greater than or equal to size requested 

        if (!GET_ALLOC(ptr) && asize <= GET_SIZE(HDRP(ptr))) {
            return ptr;
        }
    }
    return NULL;
}

// Place the requested block at the beginning of the free block
// Split only if the size of the remainder is equal or exceeds the minimum block size
static void place(void *bp, size_t asize) {

    size_t free_size = GET_SIZE(HDRP(bp));

    // Checks the remaining space in the block is large enough for the new block
    if (free_size - asize >= MINBLOCKSIZE) {

        // Splits the block; updates footer and header

        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(free_size - asize, 0));
        PUT(FTRP(bp), PACK(free_size - asize, 0));

    }
    else {
        // Allocated the entire free block 
        PUT(HDRP(bp), PACK(free_size, 1));
        PUT(FTRP(bp), PACK(free_size, 1));
    }
}