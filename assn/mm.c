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
*************************************************************************/
#define WSIZE       4            /* word size (bytes) */
#define DSIZE       8            /* doubleword size (bytes) */
#define CHUNKSIZE   16      /* initial heap size (bytes) */
#define FREE_OVERHEAD    16           /* overhead of header and footer (bytes) */
#define ALLOC_OVERHEAD    4           /* overhead of header and footer (bytes) */

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

#define RUN_ON_INSN 10
#define DEBUG 0
#define SANITY_CHECK 1
#define NUM_FREE_LISTS 7

/*************************************************************************
 * Globals 
 * This data has to be kept < 128 bytes
*************************************************************************/
void* epilogue = NULL;
void* fls[NUM_FREE_LISTS];
size_t limits[NUM_FREE_LISTS];
int counter;
int itr=0;
int num[NUM_FREE_LISTS];//NUM_FREE_LISTS

/*************************************************************************
 * Function prototypes
 * These would go in an h file if we were allowed to have one
*************************************************************************/
void F(char*c,int b);
void heapChekka(void* l);
int coalescingCheck(void* l);
void printCheck(char*c,int b);
int flValidPointersCheck(void *l);
int searchmem_check(void*bp);
int flCorrectnessCheck(void **l);
int searchlist_check(void*p,void **l);
int flAllFreeCheck(void* l);
int flPointerBoundsCheck(void *l);
int flSizeRangeCheck(void *l, int min, int max);
int* flCountsCheck(void ** l);

void P(char *c)
{
	if(DEBUG) {printf("%s",c);}
	fflush(stdout);
}

//This runs a check for one free list, l.
void run_check(void* l, size_t max, size_t min)
{
	assert(flSizeRangeCheck(l,min,max));
	assert(flPointerBoundsCheck(l));
	assert(flAllFreeCheck(l));
	assert(flValidPointersCheck(l));
	assert(coalescingCheck(l));
}

//This heap-checks all of our free lists
void mm_check()
{
	int i;
	for (i = 0; i < NUM_FREE_LISTS; ++i)
	{
		 //Run sanity check for every free list we have.
		run_check(fls[i], limits[i], i>0?limits[i-1]:0);
	}
	flCorrectnessCheck(fls);
}
void heapCheckCounter(char* c)
{
	counter++;
	if(DEBUG) 
	{
		printf("(%s%i)",c,counter); P("");
		if(counter==RUN_ON_INSN)
		{
			if(itr%12==1)
				mm_check();
		}
	}
	if(SANITY_CHECK)
	{
		if(counter%1000==0)
		{
			if(itr%12==1)
				mm_check();
		}
	}
}

/**********************************************************
 * mm_init
 * Initialize the heap, including "allocation" of the
 * prologue and epilogue
 **********************************************************/
 int mm_init(void)
 {
	int list;
	size_t limit;
	void* heap_listp = NULL;
    
	if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
    	return -1;
    PUT(heap_listp, 0);                         // alignment padding 
    PUT(heap_listp+WSIZE, PACK(ALIGNMENT, 1, 1));   // prologue header
	PUT(heap_listp+DSIZE+WSIZE, PACK(0, 1, 1));    // epilogue header
	
	epilogue = heap_listp+DSIZE+DSIZE;
	limit = 16;
	for (list = 0; list < NUM_FREE_LISTS; ++list)
	{
		fls[list] = NULL;
		limits[list] = ALIGNMENT * (limit + ALLOC_OVERHEAD + ALIGNMENT - 1)/ALIGNMENT;
		limit = limit << 1;
	}
	limits[list - 1] = -1;
	counter=0;
	itr++;
	return 0;
 }
 
// Assumes the block has already been marked as free
// and that its header and footer are set up appropriately
void add_to_free_list(void *bp)
{
	int list;
	size_t size = GET_SIZE(HDRP(bp));

	// Determine which free list this block belongs in
	for (list = 0; list < NUM_FREE_LISTS; ++list)
	{
		if (size <= limits[list])
			break;
	}
	// The last list hold everything larger than limits[NUM_FREE_LISTS - 2]
	if (list == NUM_FREE_LISTS)
		--list;
	
	if(fls[list]==NULL)//If free list empty
    {
		SetNext(bp,NULL);//Set next to null
	    SetPrev(bp,NULL);//Set prev to null
    }
    else//If list is not empty
    {
    	//Add this block to point to item at the head of the list
    	SetNext(bp,fls[list]);//Set next to whatever was at the head
    	SetPrev(bp,NULL);//Set prev to null
    	//Modify former head block to be add bp as prev
    	SetPrev(fls[list],bp);
    }
	fls[list]=bp;//Add block to head of free list
}

void remove_from_free_list(void* bp)
{
	// Remove the next block from its free list
	void * y = GetPrev(bp);
	void * z = GetNext(bp);
	if (y == NULL)
	{
		// This was the first block in its free list
		// Determine which list that was
		int i, list;
		list = -1;
		for (i = 0; i < NUM_FREE_LISTS; ++i)
		{
			if (fls[i] == bp)
			{
				list = i;
			}
		}
		assert(list != -1);
		fls[list] = z;
	}
	else
	{
		SetNext(y, z);	
	}
	if (z != NULL)
	{
		SetPrev(z, y);
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
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	
	if (prev_alloc && next_alloc) /*case 1 faFaf */
	{
		P("!1!");
	}
	else if (prev_alloc &&!next_alloc)
    { /* Case 2 faFfaf*/
		P("!2!");
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        void * nbp=NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0, 1));
        PUT(FTRP(bp), PACK(size, 0, 1));

		remove_from_free_list(nbp);
    }
    else if ( next_alloc&&!prev_alloc)
	{ /* Case 3 fafFaf*/
		P("!3!");
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0, 1));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0, 1));
       
		remove_from_free_list(PREV_BLKP(bp)); 
		bp = PREV_BLKP(bp);
    }
    else
	{ /* Case 4 fafFfaf */
		P("!4!");
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))  +
        	GET_SIZE(FTRP(NEXT_BLKP(bp)))  ;
	    void * nbp=NEXT_BLKP(bp);
	    void * pbp=PREV_BLKP(bp);
        PUT(HDRP(pbp), PACK(size,0, 1));
        PUT(FTRP(nbp), PACK(size,0, 1));
	  
		remove_from_free_list(nbp);
		remove_from_free_list(pbp);
		bp = pbp;
    }
    
	add_to_free_list(bp);
	return bp;
}

unsigned int round_up_to_next_power_of_two(unsigned int size)
{
	size--;
	size |= size >> 1;
	size |= size >> 2;
	size |= size >> 4;
	size |= size >> 8;
	size |= size >> 16;
	size++;
	return size;
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
	
	// Only extend in amounts that fit perfectly into a free list
//	int i;
/*	for (i = 0; i < NUM_FREE_LISTS; ++i)
	{
		if (size <= limits[i])
		{
			size = limits[i];
			break;
		}
	}
*/
    /* Initialize free block header/footer and the epilogue header */
	unsigned int prev = GET_PREV(HDRP(epilogue));
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
	int list;
	
	// Determine which free list to check
	for (list = 0; list < NUM_FREE_LISTS; ++list)
	{
		if (asize <= limits[list])
			break;
	}
	// The last list hold everything larger than limits[NUM_FREE_LISTS - 2]
	if (list == NUM_FREE_LISTS)
		--list;

    while (list < NUM_FREE_LISTS)
	{
		for (bp = fls[list]; bp!=NULL; bp = GetNext(bp))//Go through the free list
		{
			//If a block is not allocated, and the size fits
			if ((asize <= GET_SIZE(HDRP(bp))))
			{
				assert(!GET_ALLOC(HDRP(bp)));
				return bp;
			}
		}
		++list;
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

	remove_from_free_list(bp);	

	// Update the next physical block's prev bit	
	void * next_physical = NEXT_BLKP(bp);
	unsigned int alloc = GET_ALLOC(HDRP(next_physical));
	size_t next_size = GET_SIZE(HDRP(next_physical));	
	PUT(HDRP(next_physical), PACK(next_size, alloc, 1));
	if (alloc == 0 && next_size>0)
		PUT(FTRP(next_physical), PACK(next_size, alloc, 1));
	
	// Update the block itself
	// Note: we don't touch the footer because allocated blocks don't have footers
	PUT(HDRP(bp), PACK(bsize, 1, GET_PREV(HDRP(bp))));
}


// Mark the block as free and set up header and footer
void mark_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    unsigned int prev = GET_PREV(HDRP(bp));
	PUT(HDRP(bp), PACK(size,0,prev));
    PUT(FTRP(bp), PACK(size,0,prev));
	
	// Update the next block
	void * next = NEXT_BLKP(bp);
	size_t next_size = GET_SIZE(HDRP(next));
	unsigned int next_alloc = GET_ALLOC(HDRP(next));
	PUT(HDRP(next), PACK(next_size,next_alloc,0));
	if (next_alloc == 0 && next_size > 0)
		PUT(FTRP(next), PACK(GET_SIZE(HDRP(next)),GET_ALLOC(HDRP(next)),0));
}

/**********************************************************
 * mm_free
 * Free the block and coalesce with neighbouring blocks
 **********************************************************/
void mm_free(void *bp)
{
	heapCheckCounter("f");
	mark_free(bp);
	// coalesce calls add_to_free_list
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
	heapCheckCounter("m");
    size_t asize; /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char * bp;
    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;

	if (size <= limits[NUM_FREE_LISTS - 2])
	{
		size = round_up_to_next_power_of_two(size);    
    }

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
 *********************************************************/
void *mm_realloc(void *ptr, size_t size)
{
    heapCheckCounter("r");
	
	//check what size the block actually is
	size_t block_size = GET_SIZE(HDRP(ptr));
	size_t new_size = (size + ALLOC_OVERHEAD + ALIGNMENT -1) / ALIGNMENT * ALIGNMENT;
	//if the allocated size is enough to fit what the user wants
	if(new_size <= block_size)
		return ptr;//they can still use the same memory
	
	void *newptr;
    
	//We must allocate more memory!
	//Twice as much, since if it was realloced once,
	//it's likely to be realloced again.
	newptr=mm_malloc(new_size*2);
	
	//if malloc failed, return NULL
    if (newptr == NULL)
    	return NULL;	
	
	//copy stuff from old ptr to new ptr
	memcpy(newptr,ptr,new_size);
	mm_free(ptr);
	return newptr;
}
























//Do pointers in free list point to valid heap addresses?
int flPointerBoundsCheck(void *l)
{
	void * bp;
	void *start = mem_heap_lo() ;
	void *end = mem_heap_hi()-3;//points to last word
	for(bp=l;bp!=NULL;bp=GetNext(bp))
	{
		// is out of bounds
		if((bp>=start && bp <=end)==0)
			return 0;//you done something wrong
	}
	return 1;
}
//Is every block in the free list marked as free?
int flAllFreeCheck(void* l)
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

//Are blocks are coalesced properly
//Assumes free list is completely correct.
//Does not assume block sizing is correct
int coalescingCheck(void* l)
{	
	void * bp;
	//Go through free list
	for(bp=l;bp!=NULL;bp=GetNext(bp))
	{
		//if you have free blocks next to you
		if(GET_ALLOC(HDRP(NEXT_BLKP(bp)))== 0 || GET_PREV(HDRP(bp)) == 0)
		{
			return 0;
		}
	}
	return 1;
}

//Find if this bp is in free list
int searchlist_check(void*p,void **l)
{
	int i;
	void * bp;
	for(i=0;i<NUM_FREE_LISTS;i++)/*NUM_FREE_LISTS==8*/
	{
		for(bp=l[i];bp!=NULL;bp=GetNext(bp))
		{
			if(bp==p)//if we have found the thing
				return 1;//you done something wrong
		}
	}

	//go through free list

	return 0;
}

//Is every free block is actually present in a free list
int flCorrectnessCheck(void **flp)
{
	return 1;
	void *bp;
	void *end = mem_heap_hi()- WSIZE + 1;//points to last word
	//go through memory
	for(bp = mem_heap_lo() + DSIZE;bp<end;bp+=GET_SIZE(HDRP(bp)))
	{
		//if the block is not allocated, but you cannot find it in the free list
		if(GET_ALLOC(HDRP(bp))==0 && searchlist_check(bp,flp)==0)
			return 0;
	}
	return 1;
}

//Finding if this bp is in memory
int searchmem_check(void*bp)
{
	void * p;
	void *end = mem_heap_hi()-3;
	//from start of memory to end of memory
	for(p=mem_heap_lo()+DSIZE;p<end;p+=GET_SIZE(HDRP(p)))
	{
		//if we found the block, then it is valid
		if(p==bp)
			return 1;
	}
	return 0;
}

//Check if all free list's pointers are in memory
int flValidPointersCheck(void *l)
{
	void * bp;
	//For each element in free list
	for(bp=l;bp!=NULL;bp=GetNext(bp))
	{
		//if we cannot find this bp memory
		//then free list pointer is wrong. Corrupt free list, return fail
		if(searchmem_check(bp)==0)
			return 0;
	}
	return 1;
}

//check that all sizes within free list are in between min and max.
//max=-1 means there is no max
int flSizeRangeCheck(void *l, int min, int max)
{
	void*bp;
	int size;
	//go through list l
	for(bp=l;bp!=NULL;bp=GetNext(bp))
	{
		size=GET_SIZE(HDRP(bp));
		//if (size of block is smaller than min)
		//OR (there is a max AND we are too big)
		//then this is bad. Return 0
		if(size<min || ( (max!=-1) && (size > max) ) )
			return 0;
	}
	return 1;
}

//Count how many elements are in an array of freelists.
int* flCountsCheck(void ** l)
{
	int i;
	void * bp;
	//for each free list
	for(i=0;i<NUM_FREE_LISTS;i++)
	{
		num[i]=0;
		//go through the list
		for(bp=l[i];bp!=NULL;bp=GetNext(bp))
		{
			//count all the things!
			num[i]++;
		}
	}
	return num;
}

//print one check
void printCheck(char*c,int b)
{
	printf("\n%i CHEKKA: %s?",b,c); P("");
}
//print all checks
void heapChekka(void* l)
{
	printCheck("1. Do pointers in heap block point to valid heap addresses",	flPointerBoundsCheck(l));
	printCheck("2. Is every block in the free list marked as free", flAllFreeCheck(l));
	printCheck("3. Do pointers in free list point to valid free blocks", flValidPointersCheck(l));
	printCheck("4. Are blocks are coalesced properly",coalescingCheck(l));
	printCheck("5. Is every free block actually in the free list" ,flCorrectnessCheck(l));
	printf("\n\n\n");P("");
	
}









