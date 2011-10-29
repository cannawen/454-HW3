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
#define OVERHEAD    8           /* overhead of header and footer (bytes) */

#define MAX(x,y) ((x) > (y)?(x) :(y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)          (*(size_t *)(p))
#define PUT(p,val)      (*(size_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)

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


void* heap_listp = NULL;
void* fl=NULL;
#define DEBUG 1
int counter;

void heap_chekka(void* l);

void P(char *c)
{
	//if(DEBUG) {printf("%s",c);}
	fflush(stdout);
}
#define RUN_HEAP_CHEKKA_ON_INSN 5000
void C(char* c)
{
	if(DEBUG) {
		//printf("(%s%i)",c,counter);
		//P("");
		counter++;
		if(counter==RUN_HEAP_CHEKKA_ON_INSN)
			heap_chekka(fl);
			
	}
}
/**********************************************************
 * mm_init
 * Initialize the heap, including "allocation" of the
 * prologue and epilogue
 **********************************************************/
 int mm_init(void)
 {
    
     if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
         return -1;
     PUT(heap_listp, 0);                         // alignment padding 
     PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1));   // prologue header
     PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1));   // prologue footer
     PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1));    // epilogue header

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
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
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
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));

        if(nbp==fl)
        	fl=bp;
        	
        SetNext(bp,GetNext(nbp));
        SetPrev(bp,GetPrev(nbp));
        if(GetNext(nbp)!=NULL)
	        SetPrev(GetNext(nbp),bp);
    	if(GetPrev(nbp)!=NULL)
    		SetNext(GetPrev(nbp),bp);
        return (bp);
    }

    else if ( next_alloc&&!prev_alloc) { /* Case 3 fafFaf*/
    P("!3!");
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        
        return (PREV_BLKP(bp));
    }

    else { /* Case 4 fafFfaf */
		P("!4!");
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))  +
        	GET_SIZE(FTRP(NEXT_BLKP(bp)))  ;
	    void * nbp=NEXT_BLKP(bp);
	    void * pbp=PREV_BLKP(bp);
        PUT(HDRP(pbp), PACK(size,0));
        PUT(FTRP(nbp), PACK(size,0));
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
    PUT(HDRP(bp), PACK(size, 0));                // free block header
    PUT(FTRP(bp), PACK(size, 0));                // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));        // new epilogue header

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
    
	PUT(HDRP(bp), PACK(bsize, 1));
    PUT(FTRP(bp), PACK(bsize, 1));
}


// Mark the block as free and set up header and footer
void mark_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
}

/**********************************************************
 * mm_free
 * Free the block and coalesce with neighbouring blocks
 **********************************************************/
void mm_free(void *bp)
{
	C("f");
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
	C("m");
    size_t asize; /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char * bp;
    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = DSIZE + OVERHEAD;
    else
        asize = ALIGNMENT * ((size + (OVERHEAD) + (ALIGNMENT-1))/ ALIGNMENT);

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
    C("r");
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
























//check if bp is within bounds of heap
int freelistbounds_check(void *l)
{
	void * bp;
	void *start = mem_heap_lo();
	void *end = mem_heap_hi()-3;//points to last word
	for(bp=l;bp!=NULL;bp=GetNext(bp))
	{
		// is out of bounds
		if( ( (bp>=start) && (bp <=end) ) ==0 )
			return 0;//you done something wrong
	}
	return 1;
}
//Check that all blocks in freelist are in fact free,
int freelist_check(void* l)
{
	void * bp;
	for(bp=l;bp!=NULL;bp=GetNext(bp))
	{
		//if this block is allocated
		if(GET_ALLOC(HDRP(bp))==1)
			return 0;//you done something wrong
	}
	return 1;
}

//All blocks are coalesced properly
int coalescing_check(void* l)
{
	void * bp;
	for(bp=l;bp!=NULL;bp=GetNext(bp))
	{
		//if you have free blocks next to you
		if(GET_ALLOC(NEXT_BLKP(bp))== 0 || GET_ALLOC(PREV_BLKP(bp))== 0)
			return 0;
	}
	return 1;
}

//Find if this bp is in free list
int find_check(void*p,void *l)
{
	void * bp;
	for(bp=l;bp!=NULL;bp=GetNext(bp))
	{
		if(bp==p)//if we have found the thing
			return 0;//you done something wrong
	}
	return 1;
}

//Check if all free blocks are in free list
int allfreeinfl_check(void *l)
{
	void *bp = mem_heap_lo();
	void *end = mem_heap_hi()-3;//points to last word
	for(;bp<end;bp+=GET_SIZE(HDRP(bp)))
	{
		//if the block is not allocated, but you cannot find it in the free list
		if(GET_ALLOC(HDRP(bp))==0 && find_check(bp,fl)==0)
			return 0;
	}
	return 1;
}

void F(char*c,int b)
{
	printf("\nCHECK %s: %i",c,b); P("");
}
void heap_chekka(void* l)
{
	F("All blocks in fl are valid",	freelistbounds_check(l));
	F("All blocks in fl are free",freelist_check(l));
	F("All blocks in fl are properly coalesced",coalescing_check(l));
	F("All free blocks are in fl",allfreeinfl_check(l));
	
}








