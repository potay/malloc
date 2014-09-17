/*
 * mm.c
 * hbovik - Harry Bovik
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a full description of your solution.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"


// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                             printf("Checkheap failed on line %d\n", __LINE__);\
                             exit(-1);  \
                        }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif

/*
 * If NEXT_FIT defined use next fit search, else use first fit search
 */
#define NEXT_FITx

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
//#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc, prev_alloc)  (((size) | (alloc)) | ((prev_alloc<<1) & 0x2))
#define PACK_PREV_ALLOC(p, alloc)   ((GET(p) & ~(2)) | (alloc << 1))

/* Read and write a word at address p */
#define GET(p)                  (*(unsigned int *)(p))
#define PUT(p, val)             (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_PREV_ALLOC(p) ((GET(p)>>1) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
/* $end mallocmacros */

/* Global variables */
static unsigned int CHUNKSIZE;
static char *heap_listp = 0;  /* Pointer to first block */
static char *heap_start;

#define BUCKETS         21
#define BUCKET_LOWER    6
static char *bucketp;
static unsigned int bucket_stats[BUCKETS];

#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif

#define LHDR(bucket)    ((char *)(bucketp) + (bucket*DSIZE))
#define LFTR(bucket)    ((char *)(bucketp) + (bucket*DSIZE) + WSIZE)

#define NHDR(bp)        ((char *)(bp))
#define NFTR(bp)        ((char *)(bp) + WSIZE)

/* Given node address offset (unsigned int), compute node address (char *) */
#define NADD(p)         (heap_start + p)

/* Given node address (char *), compute node address offset (unsigned int) */
#define NREF(p)         ((unsigned int)((long)p - (long)heap_start))

/* Explicit list helper functions */
static inline char *node_prev(char *node) {
    return NADD(GET(NHDR(node)));
}

static inline char *node_next(char *node) {
    return NADD(GET(NFTR(node)));
}

static inline unsigned int get_bucket(size_t size) {
    unsigned int count = 0;
    if (size < (1 << BUCKET_LOWER)) return 0;
    while (size > 0) {
        size = size>>1;
        count++;
    }
    count += ((size - (1<<count) > 0) ? 1:0);
    count -= BUCKET_LOWER;
    return ((count < BUCKETS) ? count : (BUCKETS - 1));
}

static inline void node_insert(char *node) {
    unsigned int bucket = get_bucket(GET_SIZE(HDRP(node)));
    bucket_stats[bucket] += 1;
    if (GET(LHDR(bucket)) == 0 && GET(LFTR(bucket)) == 0) {
        PUT(LHDR(bucket), NREF(node));
        PUT(LFTR(bucket), NREF(node));
        PUT(NHDR(node), 0);
        PUT(NFTR(node), 0);
    } else {
        PUT(NFTR(NADD(GET(LFTR(bucket)))), NREF(node));
        PUT(NHDR(node), GET(LFTR(bucket)));
        PUT(NFTR(node), 0);
        PUT(LFTR(bucket), NREF(node));
    }
}

static inline void node_delete(char *node) {
    unsigned int bucket = get_bucket(GET_SIZE(HDRP(node)));
    if (GET(LHDR(bucket)) == NREF(node))
        PUT(LHDR(bucket), GET(NFTR(node)));
    else
        PUT(NFTR(node_prev(node)), GET(NFTR(node)));
    if (GET(LFTR(bucket)) == NREF(node))
        PUT(LFTR(bucket), GET(NHDR(node)));
    else
        PUT(NHDR(node_next(node)), GET(NHDR(node)));
}

static inline void printwholelist(void) {
    unsigned int bucket = 0;
    while (bucket < BUCKETS) {
        printf("Bucket %d (%x|%x): ", bucket, (GET(LHDR(bucket))), GET(LFTR(bucket)));
        if (GET(LHDR(bucket)) == 0 && GET(LFTR(bucket)) == 0) {
            printf("\n");
            bucket++;
            continue;
        } else {
            char *curr = NADD(GET(LHDR(bucket)));
            while (curr != NADD(GET(LFTR(bucket)))) {
                printf("%p -> ", (void *)curr);
                curr = node_next(curr);
            }
            printf("%p\n", NADD(GET(LFTR(bucket))));
        }
        bucket++;
    }
}

static inline void printwholeheap(void) {
    printf("Heap (%p|%p): ", (void *)mem_heap_lo(), (void *)mem_heap_hi());
    char *curr = NEXT_BLKP(heap_listp);
    while (GET_SIZE(HDRP(curr)) > 0) {
        printf("%c|%c|%p :: ", (GET_ALLOC(HDRP(curr)) ? 'a':'f'), (GET_PREV_ALLOC(HDRP(curr)) ? 'a':'f'), (void *)curr);
        curr = NEXT_BLKP(curr);
    }
    printf("\n");
}

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
int mm_checkheap(int verbose);

/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk((BUCKETS*2+4)*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */

    /* Size class: >= 2**(bucket_no + 4) */
    bucketp = heap_listp + WSIZE;

    for (unsigned int i = 0; i < BUCKETS; i++) {
        //printf("bucket %d: %d\n", i, bucket_stats[i]);
        PUT(bucketp + i*DSIZE, 0);
        PUT(bucketp + i*DSIZE + WSIZE, 0);
    }
    //printf("\n");

    PUT(heap_listp + ((BUCKETS*2+1)*WSIZE), PACK(DSIZE, 1, 0)); /* Prologue header */
    PUT(heap_listp + ((BUCKETS*2+2)*WSIZE), PACK(DSIZE, 1, 0)); /* Prologue footer */
    PUT(heap_listp + ((BUCKETS*2+3)*WSIZE), PACK(0, 1, 1));     /* Epilogue header */
    heap_listp += ((BUCKETS*2+2)*WSIZE);
    heap_start = (char *)mem_heap_lo();
/* $end mminit */

#ifdef NEXT_FIT
    rover = heap_listp;
#endif
/* $begin mminit */

    CHUNKSIZE = 1<<9;
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}
/* $end mminit */

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
/* $begin mmmalloc */
void *malloc(size_t size)
{
    //printwholelist();
    //printwholeheap();
    //printf("\n");
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

/* $end mmmalloc */
    if (heap_listp == 0){
        mm_init();
    }
/* $begin mmmalloc */
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= (DSIZE+WSIZE))
        asize = 2*DSIZE;
    else
    asize = DSIZE * ((size + (WSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}
/* $end mmmalloc */

/*
 * mm_free - Free a block
 */
/* $begin mmfree */
void free(void *bp)
{
    //printwholelist();
    //printwholeheap();
    //printf("\n");
/* $end mmfree */
    if(bp == 0)
        return;

/* $begin mmfree */
    size_t size = GET_SIZE(HDRP(bp));
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
/* $end mmfree */
    if (heap_listp == 0){
        mm_init();
    }
/* $begin mmfree */
    //printf("ftbp: %p\n", (void *)FTRP(bp));
    PUT(HDRP(bp), PACK(size, 0, prev_alloc));
    PUT(FTRP(bp), PACK(size, 0, prev_alloc));
    coalesce(bp);
}

/* $end mmfree */
/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
/* $begin mmfree */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        PUT(HDRP(NEXT_BLKP(bp)), PACK_PREV_ALLOC(HDRP(NEXT_BLKP(bp)), 0));
        node_insert(bp);
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        node_delete(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0, 1));
        PUT(FTRP(bp), PACK(size, 0, 1));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        //printf("pbp: %p\n", (void *)PREV_BLKP(bp));
        node_delete(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0, GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)))));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0, GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)))));
        bp = PREV_BLKP(bp);
        PUT(HDRP(NEXT_BLKP(bp)), PACK_PREV_ALLOC(HDRP(NEXT_BLKP(bp)), 0));
    }

    else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        node_delete(PREV_BLKP(bp));
        node_delete(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0, GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)))));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0, GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)))));
        bp = PREV_BLKP(bp);
        PUT(HDRP(NEXT_BLKP(bp)), PACK_PREV_ALLOC(HDRP(NEXT_BLKP(bp)), 0));
    }
    node_insert(bp);
/* $end mmfree */
#ifdef NEXT_FIT
    /* Make sure the rover isn't pointing into the free block */
    /* that we just coalesced */
    if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp)))
        rover = bp;
#endif
/* $begin mmfree */
    return bp;
}
/* $end mmfree */

/*
 * mm_realloc - Naive implementation of realloc
 */
void *realloc(void *ptr, size_t size)
{
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) oldsize = size;
        memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    mm_free(ptr);

    return newptr;
}

void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    char *block;

    block = malloc(bytes);
    memset(block, 0, bytes);

    return block;
}

/*
 * The remaining routines are internal helper routines
 */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0, prev_alloc));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0, prev_alloc));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1, 0)); /* New epilogue header */

    CHUNKSIZE += 16;

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
/* $end mmextendheap */

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
     /* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(bp));
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    //printf("%p:%p\n", (void *)NADD(list_header), (void *)NADD(list_footer));
    node_delete(bp);

    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1, prev_alloc));
        PUT(FTRP(bp), PACK(asize, 1, prev_alloc));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0, 1));
        PUT(FTRP(bp), PACK(csize-asize, 0, 1));
        PUT(HDRP(NEXT_BLKP(bp)), PACK_PREV_ALLOC(HDRP(NEXT_BLKP(bp)), 0));
        node_insert(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1, prev_alloc));
        PUT(FTRP(bp), PACK(csize, 1, prev_alloc));
        PUT(HDRP(NEXT_BLKP(bp)), PACK_PREV_ALLOC(HDRP(NEXT_BLKP(bp)), 1));
    }
}
/* $end mmplace */

/*
 * find_fit - Find a fit for a block with asize bytes
 */
/* $begin mmfirstfit */
/* $begin mmfirstfit-proto */
static void *find_fit(size_t asize)
/* $end mmfirstfit-proto */
{
/* $end mmfirstfit */

#ifdef NEXT_FIT
    /* Next fit search */
    char *oldrover = rover;

    /* Search from the rover to the end of list */
    for ( ; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    /* search from start of list to old rover */
    for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    return NULL;  /* no fit found */
#else
/* $begin mmfirstfit */
    /* First fit search */
    //char *bp;
    unsigned int bucket;
    unsigned int curr;
    unsigned int best = 0;
    unsigned int diff = 0;
    unsigned int found = 0;
/*
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
*/
    bucket = get_bucket(asize);
    while (bucket < BUCKETS) {
        curr = GET(LHDR(bucket));
        while (curr != 0) {
            if (!GET_ALLOC(HDRP(NADD(curr)))&&(asize <= GET_SIZE(HDRP(NADD(curr))))) {
                if ((GET_SIZE(HDRP(NADD(curr))) == asize))
                    return (void *)NADD(curr);
                if ((diff == 0) | ((GET_SIZE(HDRP(NADD(curr))) - asize) < diff)) {
                    //printf("diff: %d, ", diff);
                    best = curr;
                    diff = GET_SIZE(HDRP(NADD(curr))) - asize;
                    //printf("diff: %d\n", diff);
                    found++;
                }
                if (found >= 1)
                    return (void *)NADD(best);
            }
            curr = NREF(node_next(NADD(curr)));
        }
        if (found >= 1)
            return (void *)NADD(best);
        bucket += 1;
    }
    return ((best == 0) ? NULL : (void *)NADD(best)); /* No fit */
/* $end mmfirstfit */
#endif
}

/*
 * checkheap - Minimal check of the heap for consistency
 */
int mm_checkheap(int verbose)
{
    /*char *bp = heap_listp;

    if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose)
            printblock(bp);
        checkblock(bp);
    }

    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");*/
    verbose = verbose;
    return 0;
}
