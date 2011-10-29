/*
 * This implementation replicates the implicit list implementation
 * provided in the textbook
 * "Computer Systems - A Programmer's Perspective"
 * Blocks are never coalesced or reused. 
 * Realloc is implemented directly using mm_malloc and mm_free.
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
    "derp",
    /* First member's full name */
    "Canna Wen",
    /* First member's email address */
    "canna.wen@utoronto.ca",
    /* Second member's full name (leave blank if none) */
    "Joseph Garvey",
    /* Second member's email address (leave blank if none) */
    "joe.garvey@utoronto.ca"
};

/*************************************************************************
 * Basic Constants and Macros
 * You are not required to use these macros but may find them helpful.
*************************************************************************/
#define WSIZE       4            /* word size (bytes) */
#define DSIZE       8            /* doubleword size (bytes) */
#define CHUNKSIZE   (1<<7)      /* initial heap size (bytes) */
#define FREE_OVERHEAD    8           /* overhead of header and footer (bytes) */
#define ALLOC_OVERHEAD    8           /* overhead of header and footer (bytes) */

#define MAX(x,y) ((x) > (y)?(x) :(y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc, prev) ((size) | (alloc) | (prev << 1))

/* Read and write a word at address p */
#define GET(p)          (*(size_t *)(p))
#define PUT(p,val)      (*(size_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)
#define GET_PREV(p)		((GET(p) & 0x2) >> 1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*Address of next and previous pointers, given a bp*/
#define NEXTP(bp) HDRP(bp)+4
#define PREVP(bp) HDRP(bp)+8
/*Getting and setting values of next and previous locations
bp: pointer
Get returns value*/
#define GetNext(bp) (void *)(GET(NEXTP(bp)))
#define GetPrev(bp) (void *)(GET(PREVP(bp)))
#define SetNext(bp,val) PUT(NEXTP(bp),(size_t)val)
#define SetPrev(bp,val) PUT(PREVP(bp),(size_t)val)


void* epilogue = NULL;
void* fl=NULL;
#define DEBUG 1
int counter;


void P(char *c)
{
	printf("%s",c); fflush(stdout);
}
/**********************************************************
 * mm_init
 * Initialize the heap, including "allocation" of the
 * prologue and epilogue
 **********************************************************/
 int mm_init(void)
 {
	void* heap_listp = NULL;
    
	if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
    	return -1;
    PUT(heap_listp, 0);                         // alignment padding 
    PUT(heap_listp+WSIZE, PACK(FREE_OVERHEAD, 1, 1));   // prologue header
    PUT(heap_listp+DSIZE, PACK(FREE_OVERHEAD, 1, 1));   // prologue footer
	PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1, 1));    // epilogue header
	
	epilogue = heap_listp+WSIZE+DSIZE;
	fl=NULL;
	counter=4;
     return 0;
 }
 
// Assumes the block has already been marked as free
// and that it's header and footer are set up appropriately
void add_to_free_list(void *bp)
{
    if(fl==NULL)//If free list empty
    {

        fl=bp;//Add block to freed list
		SetNext(bp,NULL);//Set next to null
	//	printf("\n%u has now set next to %u\n",bp,GetNext(bp));P("");
	    SetPrev(bp,NULL);//Set prev to null
    }
    else//If list is full
    {
    	//Add this block to the head of the list
    	SetNext(bp,fl);//Set next to whatever was at the head
    	SetPrev(bp,NULL);//Set prev to null
    	//Modify former head block to be add bp as prev
    	SetPrev(fl,bp);
    	//Set this block as new head
    	fl=bp;
    }
}

/**********************************************************
 * coalesce
 * Covers the 4 cases discussed in the text:
 * - both neighbours are allocated
 * - the next block is available for coalescing
 * - the previous block is available for coalescing
 * - both neighbours are available for coalescing
 **********************************************************/
void *coalesce(void *bp)
{
	unsigned int prev_alloc = GET_PREV(HDRP(bp));
	printf("prev is: %u\n", prev_alloc); fflush(stdout);
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
	
	if (prev_alloc && next_alloc) /*case 1 faFaf */
	{
    	add_to_free_list(bp);
		return bp;
	}
    else if (prev_alloc &&!next_alloc)
    { /* Case 2 faFfaf*/
	    P("!2!");
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        void * nbp=NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0, 1));
        PUT(FTRP(bp), PACK(size, 0, 1));

        if(nbp==fl)
        	fl=bp;
        	
        SetNext(bp,GetNext(nbp));
        SetPrev(bp,GetPrev(nbp));
        if(GetNext(nbp)!=NULL)
	        SetPrev(GetNext(nbp),bp);
    	if(GetPrev(nbp)!=NULL)
    		SetNext(GetPrev(nbp),bp);
		P("end2");
        return (bp);
    }

    else if ( next_alloc&&!prev_alloc) { /* Case 3 fafFaf*/
    P("!3!");
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0, 1));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0, 1));
        
        return (PREV_BLKP(bp));
    }

    else { /* Case 4 fafFfaf */
		P("!4!");
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))  +
        	GET_SIZE(FTRP(NEXT_BLKP(bp)))  ;
	    void * nbp=NEXT_BLKP(bp);
	    void * pbp=PREV_BLKP(bp);
        PUT(HDRP(pbp), PACK(size,0, 1));
        PUT(FTRP(nbp), PACK(size,0, 1));
       /*printf("1\n%u\n",GetPrev(bp)); fflush(stdout);
        printf("2\n%u\n",GetNext(bp)); fflush(stdout);
        printf("3\n%u\n",GetNext(GetNext(bp))); fflush(stdout);
		if(GetPrev(bp)!=NULL)
	        SetNext(GetPrev(bp),GetNext(GetNext(bp)));
        if(GetNext(GetNext(bp))!=NULL)
	        SetPrev(GetNext(GetNext(bp)),GetPrev(bp));*/
	   
		void * y = GetPrev(nbp);
		void * z = GetNext(nbp);

		if (y == NULL)
		{
			assert(nbp ==fl);
			fl = z;
		}
		else
		{
			SetNext(y, z);	
		}
		if (z != NULL)
		{
			SetPrev(z, y);
		}
 
        return pbp;
    }
}


void *removend(void*bp)
{
	if(bp==fl)
		fl=NULL;
	else
		SetNext(GetPrev(bp),NULL);
	return bp;
}

/**********************************************************
 * extend_heap
 * Extend the heap by "words" words, maintaining alignment
 * requirements of course. Free the former epilogue block
 * and reallocate its new header
 **********************************************************/
void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignments */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ( (bp = mem_sbrk(size)) == NULL )
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
	unsigned int prev = GET_PREV(epilogue);
	PUT(HDRP(bp), PACK(size, 0, prev));                // free block header
    PUT(FTRP(bp), PACK(size, 0, prev));                // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1, 0));        // new epilogue header

	epilogue = NEXT_BLKP(bp);
	
	/* Coalesce if the previous block was free */
    return coalesce(bp);
}


/**********************************************************
 * find_fit
 * Traverse the heap searching for a block to fit asize
 * Return NULL if no free blocks can handle that size
 * Assumed that asize is aligned
 **********************************************************/
void * find_fit(size_t asize) 
{
    void *bp;
	
/*
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        }
    }
    return NULL;*/
    for (bp = fl; bp!=NULL; bp = GetNext(bp))//Go through the free list
    {
    	//printf("%u has next set to %u\n",bp,GetNext(bp));P("");
		//If a block is not allocated, and the size fits
        if ((asize <= GET_SIZE(HDRP(bp))))
        {
			assert(!GET_ALLOC(bp));
			return bp;        	
		}
	}

    return NULL;
}

/**********************************************************
 * place
 * Mark the block as allocated
 **********************************************************/
void place(void* bp, size_t asize)//doesn't even use asize: terrible, just uses 128
{
    /* Get the current block size */
    size_t bsize = GET_SIZE(HDRP(bp));

	void *p = GetPrev(bp);
  	void *n = GetNext(bp);
	
	if(p==NULL&&n==NULL)//only one element
	{
		fl=NULL;
    }
    else if(p!=NULL && n==NULL)//at the end of list
    {
    	SetNext(p,n);//set NULL to previousBlock->nextFree
	}
    else if(p==NULL&&n!=NULL)//at the start of the linked list
    {
    	SetPrev(n,p);//Set nextBlock->prevFree=NULL, meaning it is at the head of the linked list
    	fl=n;
    }
    else//if we are in the middle
    {
    	SetNext(p,n);
    	SetPrev(n,p);
    }
  
	void * next_physical = NEXT_BLKP(bp);
	unsigned int alloc = GET_ALLOC(next_physical);
	size_t next_size = GET_SIZE(next_physical);	
	PUT(HDRP(next_physical), PACK(next_size, alloc, 1));
	if (alloc == 0)
		PUT(FTRP(next_physical), PACK(next_size, alloc, 1));
	
	PUT(HDRP(bp), PACK(bsize, 1, GET_PREV(bp)));
}


// Mark the block as free and set up header and footer
void mark_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    unsigned int prev = GET_PREV(HDRP(bp));
	PUT(HDRP(bp), PACK(size,0,prev));
    PUT(FTRP(bp), PACK(size,0,prev));
}

/**********************************************************
 * mm_free
 * Free the block and coalesce with neighbouring blocks
 **********************************************************/
void mm_free(void *bp)
{
	P("f");
	//add_to_free_list(bp);
    mark_free(bp);
	// coalesce calls add_to_free_list
	
	//add_to_free_list(bp);
	coalesce(bp);
}


/**********************************************************
 * mm_malloc
 * Allocate a block of size bytes.
 * The type of search is determined by find_fit
 * The decision of splitting the block, or not is determined
 *   in place(..)
 * If no block satisfies the request, the heap is extended
 **********************************************************/
void *mm_malloc(size_t size)
{
    size_t asize; /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char * bp;
	P("m");if(DEBUG) {printf("%i ",counter);counter++;}
    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = DSIZE + ALLOC_OVERHEAD;
    else
        asize = ALIGNMENT * ((size + (ALLOC_OVERHEAD) + (ALIGNMENT-1))/ ALIGNMENT);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);//this is terrible
    // NOTE: extend_heap adds the new space to the free list
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
    {
		return NULL;
    }
    place(bp, asize);//horrible
	//printf("m:%u\n",(unsigned int)bp); P("");
    return bp;
}

/**********************************************************
 * mm_realloc
 * Implemented simply in terms of mm_malloc and mm_free
 *********************************************************/
void *mm_realloc(void *ptr, size_t size)
{
    P("realloc\n");
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;

    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

