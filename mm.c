/*
 * mm.c
 *
 * Du Shangchen 1600012782
 * Use segregated free list
 *
 *
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
# define dbg_//printf(...) //printf(__VA_ARGS__)
#else
# define dbg_//printf(...)
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
#define CHUNKSIZE  160  /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global variables */
static char * heap_listp = 0;  /* Pointer to first block */

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);

/* Convert 4-byte address to 8-byte address */
static inline void * word_to_ptr(unsigned int w)
{
    return ((w) == 0 ? NULL : (void *)((unsigned int)(w) + 0x800000000UL));
}

/* Convert 8-byte address to 4-byte address */
static inline unsigned int ptr_to_word(void * p)
{
    return ((p) == NULL ? 0 : (unsigned int)((unsigned long)(p) - 0x800000000UL));
}


/* My global variables */
void **list_addr = 0;
/* End my global */

/* My macros */
#define LIST_NUM  16
#define NEXT_LINK(bp)  (* (unsigned int *)(bp))
#define PREV_LINK(bp)  (* (unsigned int *)(bp + WSIZE))
/* End my macros */

/* My functions */
static void add_block(void *bp);
static void del_block(void *bp);
int getNumber(size_t size);
void checkblock(void *bp);
void printblock(void *bp);
/* End my functions */


/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void)
{
    list_addr = mem_sbrk(ALIGN(WSIZE * 4 + LIST_NUM * sizeof(void *)));
    if (list_addr == (void *)-1)
        return -1;
    heap_listp = (char *)list_addr + sizeof(void *) * LIST_NUM;

    int i;
    for (i = 0; i < LIST_NUM; i++)
        list_addr[i] = NULL;
    for (i = 0; i < LIST_NUM; i++)

    PUT(heap_listp, 0);
    PUT(heap_listp + WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + 2 * WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + 3 * WSIZE, PACK(0, 1));
    heap_listp += 2 * WSIZE;

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * malloc
 */
void *malloc (size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    if (heap_listp == 0){
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
    {
        return NULL;
    }

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

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

/*
 * free
 */
void free (void *bp)
{
    if (bp == 0)
        return;

    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0){
        mm_init();
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * realloc - you may want to look at mm-naive.c
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



/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size)
{
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
void mm_checkheap(int verbose)
{
    char *bp = heap_listp;
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
        printf("Bad epilogue header\n");
}


 /*
  * extend_heap - Extend heap with free block and return its block pointer
  */
 static void *extend_heap(size_t words)
 {
     char *bp;
     size_t size;

     size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
     if ((long)(bp = mem_sbrk(size)) == -1)
     {
         return NULL;
     }

     /* Initialize free block header/footer and the epilogue header */
     PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
     PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
     PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
     PREV_LINK(bp) = 0;
     NEXT_LINK(bp) = 0;
     /* Coalesce if the previous block was free */
     return coalesce(bp);
 }

 /*
  * coalesce - Boundary tag coalescing. Return ptr to coalesced block
  */
 static void *coalesce(void *bp)
 {
     size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
     size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
     size_t size = GET_SIZE(HDRP(bp));

     if (prev_alloc && next_alloc);             /* Case 1 */

     else if (prev_alloc && !next_alloc) {      /* Case 2 */
         del_block(NEXT_BLKP(bp));
         size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
         PUT(HDRP(bp), PACK(size, 0));
         PUT(FTRP(bp), PACK(size,0));
     }

     else if (!prev_alloc && next_alloc) {      /* Case 3 */
         del_block(PREV_BLKP(bp));
         size += GET_SIZE(HDRP(PREV_BLKP(bp)));
         PUT(FTRP(bp), PACK(size, 0));
         PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
         bp = PREV_BLKP(bp);
     }

     else {                                     /* Case 4 */
         size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
             GET_SIZE(FTRP(NEXT_BLKP(bp)));
         del_block(NEXT_BLKP(bp));
         del_block(PREV_BLKP(bp));
         PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
         PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
         bp = PREV_BLKP(bp);
     }
     PREV_LINK(bp) = 0;
     NEXT_LINK(bp) = 0;
     add_block(bp);
     return bp;
 }

 /*
  * place - Place block of asize bytes at start of free block bp
  *         and split if remainder would be at least minimum block size
  */
 static void place(void *bp, size_t asize)
 {
    size_t csize = GET_SIZE(HDRP(bp));
    del_block(bp);
    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        PREV_LINK(bp) = 0;
        NEXT_LINK(bp) = 0;
        add_block(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
 }

 /*
 * find_fit - Find a fit for a block with asize bytes
 */
 static void *find_fit(size_t asize)
 {
    int number = getNumber(asize);
    void *addr;

    while (number < LIST_NUM)
    {
        addr = list_addr[number];
        while (addr != NULL)
        {
            if (GET_SIZE(HDRP(addr)) >= asize)
            {
                return addr;
            }
            addr = word_to_ptr(NEXT_LINK(addr));
        }
        number++;
    }
    return NULL;
 }

 /* My functions */

/*
 * Add a block into a suitable list
 */
static void add_block(void *bp)
 {
     size_t size = GET_SIZE(HDRP(bp));
     int number = getNumber(size);
     if (list_addr[number] == NULL)
     {
         list_addr[number] = bp;

         PREV_LINK(bp) = 0;
         NEXT_LINK(bp) = 0;
     }
     else
     {
         void *addr = list_addr[number];
         list_addr[number] = bp;
         PREV_LINK(bp) = 0;
         NEXT_LINK(bp) = ptr_to_word(addr);
         PREV_LINK(addr) = ptr_to_word(bp);
     }
}

 /*
  * Delete a block which is free from its list
  */
static void del_block(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    int number = getNumber(size);
    int prev = (int)PREV_LINK(bp);
    int next = (int)NEXT_LINK(bp);
    if (prev == 0 && next == 0)
    {
        list_addr[number] = NULL;
    }
    else if (prev == 0 && next != 0)
    {
        list_addr[number] = word_to_ptr(NEXT_LINK(bp));
        PREV_LINK(word_to_ptr(NEXT_LINK(bp))) = 0;
    }
    else if (prev != 0&& next == 0)
    {
        NEXT_LINK(word_to_ptr(PREV_LINK(bp))) = 0;
        PREV_LINK(bp) = 0;
    }
    else
    {
        PREV_LINK(word_to_ptr(NEXT_LINK(bp))) = PREV_LINK(bp);
        NEXT_LINK(word_to_ptr(PREV_LINK(bp))) = NEXT_LINK(bp);
    }
}

/*
 * Get the number of list where the block is
 */
int getNumber(size_t  size)
{
    int number;
    for (number = 0; number < LIST_NUM-1; number++)
    {
        if ((unsigned)(1 << (number + 4)) >= size)
        {
            return number;
        }
    }
    return number;
}

/*
 * Print information of each block
 */
void printblock(void *bp)
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0) {
    printf("%p: EOL\n", bp);
    return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp,
       (int)hsize, (halloc ? 'a' : 'f'),
       (int)fsize, (falloc ? 'a' : 'f'));
}

void checkblock(void *bp)
{
    if ((size_t)bp % 8)
    printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
    printf("Error: header does not match footer\n");
}
