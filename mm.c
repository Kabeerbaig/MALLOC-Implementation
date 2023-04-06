/*
 * Simple, 64-bit allocator based on implicit free lists,
 * first fit placement, and boundary tag coalescing, as described
 * in the CS:APP2e text. Blocks must be aligned to 16 byte
 * boundaries. Minimum block size is 16 bytes.
 *
 * This version is loosely based on
 * http://csapp.cs.cmu.edu/3e/ics3/code/vm/malloc/mm.c
 * but unlike the book's version, it does not use C preprocessor
 * macros or explicit bit operations.
 *
 * It follows the book in counting in units of 4-byte words,
 * but note that this is a choice (my actual solution chooses
 * to count everything in bytes instead.)
 *
 * You should use this code as a starting point for your
 * implementation.
 *
 * First adapted for CS3214 Summer 2020 by gback
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <assert.h>

#include "mm.h"
#include "list.h"
#include "memlib.h"
#include "config.h"

struct boundary_tag
{
    int inuse : 1; // inuse bit
    int size : 31; // size of block, in words
                   // block size
};

/* FENCE is used for heap prologue/epilogue. */
const struct boundary_tag FENCE = {
    .inuse = 1,
    .size = 0};

/* A C struct describing the beginning of each block.
 * For implicit lists, used and free blocks have the same
 * structure, so one struct will suffice for this example.
 *
 * If each block is aligned at 12 mod 16, each payload will
 * be aligned at 0 mod 16.
 */
struct block
{
    struct boundary_tag header; /* offset 0, at address 12 mod 16 */
    char payload[0];            /* offset 4, at address 0 mod 16 */
    struct list_elem list_elem; // pointers
};

/* Basic constants and macros */
#define WSIZE sizeof(struct boundary_tag) /* Word and header/footer size (bytes) */
#define MIN_BLOCK_SIZE_WORDS 16           /* Minimum block size in words */
#define CHUNKSIZE (1 << 10)               /* Extend heap by this amount (words) */
#define NUM_OF_LISTS 17
static inline size_t max(size_t x, size_t y)
{
    return x > y ? x : y;
}

static size_t align(size_t size)
{
    return (size + ALIGNMENT - 1) & ~(ALIGNMENT - 1);
}

static bool is_aligned(size_t size) __attribute__((__unused__));
static bool is_aligned(size_t size)
{
    return size % ALIGNMENT == 0;
}

/* Global variables */
static struct block *heap_listp = 0; /* Pointer to first block */
// static  struct list free_list; // free list
static struct list free_lists[NUM_OF_LISTS]; // free lists
/* Function prototypes for internal helper routines */
static struct block *extend_heap(size_t words);
static void place(struct block *bp, size_t asize);
static struct block *find_fit(size_t asize);
static struct block *coalesce(struct block *bp);
int get_list_index(size_t size);

/* Given a block, obtain previous's block footer.
   Works for left-most block also. */
static struct boundary_tag *prev_blk_footer(struct block *blk)
{
    return &blk->header - 1;
}

/* Return if block is free */
static bool blk_free(struct block *blk)
{
    return !blk->header.inuse;
}

/* Return size of block is free */
static size_t blk_size(struct block *blk)
{
    return blk->header.size;
}

/* Given a block, obtain pointer to previous block.
   Not meaningful for left-most block. */
static struct block *prev_blk(struct block *blk)
{
    struct boundary_tag *prevfooter = prev_blk_footer(blk);
    assert(prevfooter->size != 0);
    return (struct block *)((void *)blk - WSIZE * prevfooter->size);
}

/* Given a block, obtain pointer to next block.
   Not meaningful for right-most block. */
static struct block *next_blk(struct block *blk)
{
    assert(blk_size(blk) != 0);
    return (struct block *)((void *)blk + WSIZE * blk->header.size);
}

/* Given a block, obtain its footer boundary tag */
static struct boundary_tag *get_footer(struct block *blk)
{
    return ((void *)blk + WSIZE * blk->header.size) - sizeof(struct boundary_tag);
}

/* Set a block's size and inuse bit in header and footer */
// need to use this for realloc, not mark_block_used
static void set_header_and_footer(struct block *blk, int size, int inuse)
{
    blk->header.inuse = inuse;
    blk->header.size = size;
    *get_footer(blk) = blk->header; /* Copy header to footer */
}

/* Mark a block as used and set its size. */
static void mark_block_used(struct block *blk, int size)
{
    set_header_and_footer(blk, size, 1);
    list_remove(&blk->list_elem);
}

/* Mark a block as free and set its size. */
static void mark_block_free(struct block *blk, int size, int index)
{
    list_push_front(&free_lists[index], &blk->list_elem);
    set_header_and_footer(blk, size, 0);
}

/*
 * mm_init - Initialize the memory manager
 */
int mm_init(void)
{
    // Initialize the free list struct

    for (int i = 0; i < NUM_OF_LISTS; i++)
    {
        list_init(&free_lists[i]);
    }

    assert(offsetof(struct block, payload) == 4);
    assert(sizeof(struct boundary_tag) == 4);

    /* Create the initial empty heap */
    struct boundary_tag *initial = mem_sbrk(4 * sizeof(struct boundary_tag));
    if (initial == NULL)
        return -1;

    /* We use a slightly different strategy than suggested in the book.
     * Rather than placing a min-sized prologue block at the beginning
     * of the heap, we simply place two fences.
     * The consequence is that coalesce() must call prev_blk_footer()
     * and not prev_blk() because prev_blk() cannot be called on the
     * left-most block.
     */
    initial[2] = FENCE; /* Prologue footer */
    heap_listp = (struct block *)&initial[3];
    initial[3] = FENCE; /* Epilogue header */

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
void *mm_malloc(size_t size)
{
    struct block *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    size_t bsize = align(size + 2 * sizeof(struct boundary_tag)); /* account for tags */
    if (bsize < size)
        return NULL; /* integer overflow */

    /* Adjusted block size in words */
    size_t awords = max(MIN_BLOCK_SIZE_WORDS, bsize / WSIZE); /* respect minimum size */

    /* Search the free list for a fit */
    if ((bp = find_fit(awords)) != NULL)
    {
        place(bp, awords);
        return bp->payload;
    }

    /* No fit found. Get more memory and place the block */
    size_t extendwords = max(awords, CHUNKSIZE); /* Amount to extend heap if no fit */
    if ((bp = extend_heap(extendwords)) == NULL)
        return NULL;

    place(bp, awords);
    return bp->payload;
}

/*
 * mm_free - Free a block
 */
void mm_free(void *bp)
{
    assert(heap_listp != 0); // assert that mm_init was called
    if (bp == 0)
        return;

    /* Find block from user pointer */
    struct block *blk = bp - offsetof(struct block, payload);
    size_t size = blk_size(blk);
    int num = get_list_index(size);
    mark_block_free(blk, blk_size(blk), num);
    coalesce(blk);
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static struct block *coalesce(struct block *bp)
{
    bool prev_alloc = prev_blk_footer(bp)->inuse; /* is previous block allocated? */
    bool next_alloc = !blk_free(next_blk(bp));    /* is next block allocated? */
    size_t size = blk_size(bp);

    if (prev_alloc && next_alloc)
    { /* Case 1 */
        // both are allocated, nothing to coalesce
        return bp;
    }

    else if (prev_alloc && !next_alloc)
    { /* Case 2 */
        // combine this block and next block by extending it
        // Add size of next block to the current block

        size += blk_size(next_blk(bp));
        // mark the block free
        list_remove(&next_blk(bp)->list_elem);
        list_remove(&bp->list_elem);

        int index = get_list_index(size);
        mark_block_free(bp, size, index);
    }

    else if (!prev_alloc && next_alloc)
    { /* Case 3 */
        // combine previous and this block by extending previous

        size += blk_size(prev_blk(bp));
        list_remove(&prev_blk(bp)->list_elem);
        list_remove(&bp->list_elem);
        int index1 = get_list_index(size);
        mark_block_free(prev_blk(bp), size, index1);

        bp = prev_blk(bp);
    }

    else
    { /* Case 4 */
        // combine all previous, this, and next block into one

        size += blk_size(prev_blk(bp)) + blk_size(next_blk(bp));

        list_remove(&prev_blk(bp)->list_elem);

        list_remove(&next_blk(bp)->list_elem);
        list_remove(&bp->list_elem);
        int index2 = get_list_index(size);
        mark_block_free(prev_blk(bp), size, index2);
        // mark_block_free(next_blk(bp), size + temp_size);
        bp = prev_blk(bp);
    }
    // add the resulting blocks to free list

    return bp;
}

/*
 * mm_realloc - Naive implementation of realloc
 */
// review presentation for 6 realloc cases to look at
// 6 if cases
// case 5 will have to use extend heap
// case 2 and 3 can be the same check; make sure block is minimum block size
// Case 4 make sure black is minimum block size
void *mm_realloc(void *ptr, size_t size)
{
    struct block *blk = ptr - offsetof(struct block, payload);
    bool prev_alloc = prev_blk_footer(blk)->inuse; /* is previous block allocated? */
    bool next_alloc = !blk_free(next_blk(blk));    /* is next block allocated? */

    size_t bsize = align(size + 2 * sizeof(struct boundary_tag)); /* account for tags */
    size_t awords = max(MIN_BLOCK_SIZE_WORDS, bsize / WSIZE);     /* respect minimum size */

    /*
    CASE 0
     Original size is greater than requested size
    */
    if (blk_size(blk) >= awords)
    {
        return ptr;
    }
    /*
    Case 2,3,4
    Next block is free
    Requested size is greater than original size
        case 2&3: take up the next block if it is free
        case 4  : if space not sufficient, use the previous block if free and copy original data starting from
                  that previous spot
    */
    else if (!next_alloc)
    {
        // case 2&3
        size_t b_size = blk_size(blk) + blk_size(next_blk(blk));
        if (b_size >= awords)
        {
            list_remove(&next_blk(blk)->list_elem);

            set_header_and_footer(blk, b_size, 1);
            return &blk->payload;
        }

        // case 4
        if (!prev_alloc)
        {
            struct block *oldblock = ptr - offsetof(struct block, payload);
            struct block *prevBlk = prev_blk(oldblock);
            struct block *nextBlk = next_blk(oldblock);
            size_t b_size = blk_size(oldblock) + blk_size(prevBlk) + blk_size(nextBlk);

            if (b_size >= awords)
            {
                mark_block_used(prevBlk, b_size);
                /* Copy the old data. */
                size_t oldpayloadsize = blk_size(oldblock) * WSIZE - 2 * sizeof(struct boundary_tag);
                memmove(&prevBlk->payload, oldblock->payload, oldpayloadsize);

                return &prevBlk->payload;
            }
        }
    }
    /*
    Case 1
    Previous block is free
    Requested size is greater than original size
        case 1: copy the data into the beginning of the previous block and continue into the second block
    */
    else if (!prev_alloc)
    {
        struct block *oldblock = ptr - offsetof(struct block, payload);
        struct block *prevBlk = prev_blk(oldblock);
        size_t b_size = blk_size(oldblock) + blk_size(prevBlk);

        if (b_size >= awords)
        {
            mark_block_used(prevBlk, b_size);
            /* Copy the old data. */
            size_t oldpayloadsize = blk_size(oldblock) * WSIZE - 2 * sizeof(struct boundary_tag);
            memmove(&prevBlk->payload, oldblock->payload, oldpayloadsize);

            return &prevBlk->payload;
        }
    }

    /* If size == 0 then this is just free, and we return NULL. */
    if (size == 0)
    {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if (ptr == NULL)
    {
        return mm_malloc(size);
    }

    void *newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if (!newptr)
    {
        return 0;
    }

    /* Copy the old data. */
    struct block *oldblock = ptr - offsetof(struct block, payload);
    size_t oldpayloadsize = blk_size(oldblock) * WSIZE - 2 * sizeof(struct boundary_tag);
    if (size < oldpayloadsize)
        oldpayloadsize = size;
    memcpy(newptr, ptr, oldpayloadsize);

    /* Free the old block. */
    mm_free(ptr);

    return newptr;
}

/*
 * checkheap - We don't check anything right now.
 */
void mm_checkheap(int verbose)
{
}

/*
 * The remaining routines are internal helper routines
 */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
static struct block *extend_heap(size_t words)
{
    void *bp = mem_sbrk(words * WSIZE);

    if (bp == NULL)
        return NULL;

    /* Initialize free block header/footer and the epilogue header.
     * Note that we overwrite the previous epilogue here. */
    struct block *blk = bp - sizeof(FENCE);
    int index = get_list_index(words);
    mark_block_free(blk, words, index);
    next_blk(blk)->header = FENCE;

    /* Coalesce if the previous block was free */

    return coalesce(blk);
}

/*
 * place - Place block of asize words at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
static void place(struct block *bp, size_t asize)
{
    size_t csize = blk_size(bp);

    if ((csize - asize) >= (MIN_BLOCK_SIZE_WORDS))
    {

        mark_block_used(bp, asize);
        // list_remove(&bp->list_elem);
        struct block *next_block = next_blk(bp);
        int index = get_list_index((csize - asize));
        mark_block_free(next_block, csize - asize, index);

        // add_to_list(next_block);
    }
    else
    {
        mark_block_used(bp, csize);
        // list_remove(&bp->list_elem);
    }
}

/*
 * find_fit - Find a fit for a block with asize words
 */

static struct block *find_fit(size_t asize)
{
    /* First fit search */

    int num = get_list_index(asize);
    for (int i = num; i < NUM_OF_LISTS; i++)
    {
        int count = 0;
        for (struct list_elem *e = list_begin(&free_lists[i]); e != list_end(&free_lists[i]); e = list_next(e))
        {
            struct block *ptr = list_entry(e, struct block, list_elem);
            if (asize <= blk_size(ptr))
            {
                return ptr;
            }
            if (count++ == 8)
            {
                break;
            }
        }
    }
    return NULL;
}

team_t team = {
    /* Team */
    "Allocation Assassins",
    /* full name of first member */
    "John Tomas",
    /* login ID of first member */
    "jtomas",
    /* full name of second member (if any) */
    "Kabeer Baig",
    /* login ID of second member */
    "kabeerb"};

int get_list_index(size_t size)
{
    switch (size)
    {
    case 0 ... 16:
        return 0;
    case 17 ... 32:
        return 1;
    case 33 ... 64:
        return 2;
    case 65 ... 128:
        return 3;
    case 129 ... 256:
        return 4;
    case 257 ... 512:
        return 5;
    case 513 ... 1024:
        return 7;
    case 1025 ... 2048:
        return 8;
    case 2049 ... 4096:
        return 9;
    case 4097 ... 8192:
        return 10;
    default:
        return 11;
    }
}
// 32 and 128
// IF thery are slightly more or less add them in different lists
// TODO: how to increase throughput in seg list
// TODO: do we have to set new bondary tags?
// coalecsing, binary, realloc have low util