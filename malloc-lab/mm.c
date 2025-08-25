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
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
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
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes; 2^12 = 4,096) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7) // header, 혹은 footer의 block size를 추출
#define GET_ALLOC(p) (GET(p) & 0x1) // header, 혹은 footer의 allocate bit를 추출

/* Given block ptr bp, compute address of its header and footer */
/* malloc이 반환하는 포인터는 header 직후의 메모리 주소를 의미함 */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* ****************************************** */

/* heap의 시작 지점을 추적하는 포인터  */
static void *g_heap_listp;

/* 마지막으로 할당한 블록을 추적하는 포인터 */
static void *g_last_bp;

/* ****************************************** */

/* bp 주변 free block과 병합하는 함수 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    {
        /* Case #1 */
        g_last_bp = bp;
        return bp;
    }
    else if (prev_alloc && !next_alloc)
    {
        /* Case #2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    {
        /* Case #3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else
    {
        /* Case #4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    g_last_bp = bp;
    return bp;
}

/* heap 공간을 추가로 할당받는 함수 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }

    /* Initialize free block headre/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((g_heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    {
        return -1;
    }

    PUT(g_heap_listp, 0);                            /* Alignment padding */
    PUT(g_heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(g_heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(g_heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    g_heap_listp += (2 * WSIZE);
    g_last_bp = g_heap_listp;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return -1;
    }
    return 0;
}

/* free list에서 할당 가능한 공간이 있는지 탐색하는 함수 */
static void *find_fit(size_t asize)
{
    char *bp = NEXT_BLKP(g_heap_listp);
    while (GET_SIZE(HDRP(bp)) != 0)
    {
        if (GET_SIZE(HDRP(bp)) >= asize && GET_ALLOC(HDRP(bp)) == 0)
        {
            return bp;
        }
        bp = NEXT_BLKP(bp);
    }
    return NULL;
}

/* find_fit으로 찾은 공간에 메모리를 할당하는 함수 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    // 분할이 필요한 경우
    if ((csize - asize) >= 2 * DSIZE)
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* next-fit 메모리 할당 방식 구현 */
static void *next_fit(size_t asize)
{
    void *bp = g_last_bp;
    while (GET_SIZE(HDRP(bp)) > 0)
    {
        if (GET_ALLOC(HDRP(bp)) == 0 && GET_SIZE(HDRP(bp)) >= asize)
        {
            g_last_bp = bp;
            return bp;
        }
        bp = NEXT_BLKP(bp);
    }

    bp = NEXT_BLKP(g_heap_listp);
    while (bp < g_last_bp)
    {
        if (GET_ALLOC(HDRP(bp)) == 0 && GET_SIZE(HDRP(bp)) >= asize)
        {
            g_last_bp = bp;
            return bp;
        }
        bp = NEXT_BLKP(bp);
    }
    return NULL;
}

/* best-fit 메모리 할당 방식 구현 */
static void *best_fit(size_t asize)
{
    void *best_bp = NULL;
    size_t min_gap = __SIZE_MAX__;

    void *bp = NEXT_BLKP(g_heap_listp);
    size_t csize;
    while ((csize = GET_SIZE(HDRP(bp))) > 0)
    {
        if (GET_ALLOC(HDRP(bp)) == 0 && csize >= asize)
        {
            if (GET_SIZE(HDRP(bp)) == (unsigned int)asize)
            {
                return bp;
            }
            else
            {
                size_t gap = csize - asize;
                if (gap < min_gap)
                {
                    min_gap = gap;
                    best_bp = bp;
                }
            }
        }

        bp = NEXT_BLKP(bp);
    }

    return best_bp;
}

/*
 * mm_malloc - Implicit free list / First fit
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
    {
        return NULL;
    }

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
    {
        asize = 2 * DSIZE;
    }
    else
    {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    /* Search the free list for a fit */
    if ((bp = best_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    g_last_bp = coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
    {
        return mm_malloc(size);
    }

    if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }

    if (!GET_ALLOC(HDRP(ptr)))
    {
        return NULL;
    }

    size_t asize; /* Adjusted block size */

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
    {
        asize = 2 * DSIZE;
    }
    else
    {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    unsigned int old_size = GET_SIZE(HDRP(ptr));
    if (asize <= old_size)
    {
        // Case #1: 요청 size가 현재 size보다 작은 경우

        // 분할이 필요한 경우
        if ((old_size - asize) >= 2 * DSIZE)
        {
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));
            void *next_ptr = NEXT_BLKP(ptr);
            PUT(HDRP(next_ptr), PACK(old_size - asize, 0));
            PUT(FTRP(next_ptr), PACK(old_size - asize, 0));
        }
        else
        {
            PUT(HDRP(ptr), PACK(old_size, 1));
            PUT(FTRP(ptr), PACK(old_size, 1));
        }
        g_last_bp = ptr;
        return ptr;
    }

    void *next_ptr = NEXT_BLKP(ptr);
    unsigned int next_size = GET_SIZE(HDRP(next_ptr));
    unsigned int combined_size = old_size + next_size;
    if (GET_ALLOC(HDRP(next_ptr)) == 0 && combined_size >= asize)
    {
        // Case #2-1: next block이 free block인 경우,
        // 현재 block의 size + next block의 size가 요청 size보다 큰 경우
        PUT(HDRP(ptr), PACK(combined_size, 1));
        PUT(FTRP(ptr), PACK(combined_size, 1));
        g_last_bp = ptr;
        return ptr;
    }

    void *prev_ptr = PREV_BLKP(ptr);
    size_t prev_size = GET_SIZE(HDRP(prev_ptr));
    combined_size = old_size + prev_size;
    if (!GET_ALLOC(HDRP(prev_ptr)) && (combined_size >= asize))
    {
        // Case #2-2: prev block이 free block인 경우, (필요한가? 고민 필요)
        // 현재 block의 size + next block의 size가 요청 size보다 큰 경우
        memmove(prev_ptr, ptr, asize);

        PUT(HDRP(prev_ptr), PACK(asize, 1));
        PUT(FTRP(prev_ptr), PACK(asize, 1));
        void *next_ptr = NEXT_BLKP(prev_ptr);
        PUT(HDRP(next_ptr), PACK(combined_size - asize, 0));
        PUT(FTRP(next_ptr), PACK(combined_size - asize, 0));

        g_last_bp = prev_ptr;
        return prev_ptr;
    }

    // Case #3: 새로운 주소를 반환
    void *new_ptr = mm_malloc(size);
    if (new_ptr == NULL)
    {
        return NULL;
    }

    // 기존 데이터 복사
    unsigned int copy_size = old_size - DSIZE;
    memmove(new_ptr, ptr, copy_size);
    mm_free(ptr);
    return new_ptr;
}
