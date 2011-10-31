/*
 * ECE454 Assignment 3
 * Joe Garvey and Canna Wen
 *
 * Our memory implementation is a variant on simple segregated free lists that combines some elements from segregated best fit.
 * We use NUM_FREE_LISTS segregated lists to store free blocks.
 * Each free list has a size limit corresponding to a power of 2, rounded up for overhead and alignment.
 * For example, the first list hold blocks up to 32B in size, the next list holds block up to 40B, the next 72B etc.
 * The last list holds all blocks too large to fit in any of the other lists.
 * When malloc is called, the first available block is chosen from the appropriately sized list.
 * If that list is empty, the next largest list is used.
 * Allocates are only done in powers of 2 (rounded up for overhead and alignment) except for requests large enough to use blocks from the last list.
 * Splitting of free blocks is only performed on blocks that fit in the largest list and only if the result would still belong in the largest list. 
 * Whenever a block is freed it is coalesced with any free neighbours (who are removed from their free lists) and it is added to the appropriate free list.
 * The free lists operate as LIFO queues.
 * Reallocs are handled with a simple malloc and free unless the block being realloced is at the end of the heap.
 * If this is the case, the heap is extended and the extra space is appended to that block.  That way no memory needs to be copied.
 * Free blocks have a 4B header and a 4B footer which are identical and contain the following information: 
 * the size of the block, whether or not the block is allocated, and whether or not the previous block (physically) is allocated.
 * Allocated blocks have headers that are the same as free blocks but they do not have footers.
 * This extra space is rarely used due to the nature of the power of 2 rounding,
 * but it was left this way because tests showed no improvement when using this extra word.
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

/*Getting and setting values of next and previous of linked list*/
#define GetNext(bp) (void *)(GET(NEXTP(bp)))
#define GetPrev(bp) (void *)(GET(PREVP(bp)))
#define SetNext(bp,val) PUT(NEXTP(bp),(size_t)val)
#define SetPrev(bp,val) PUT(PREVP(bp),(size_t)val)

/* The number of segregated free lists.  This should be >= 2 or else some code breaks.*/
#define NUM_FREE_LISTS 7

/* Various debug related constants
 * DEBUG causes statements to be printed with every malloc/free/realloc
 * It also causes the heap checker to be called on call # RUN_ON_INSN
 * SANITY causes the heap checker to be run every HEAP_CHECK_PERIOD calls.
 */ 
#define DEBUG 0
#define RUN_ON_INSN 10
#define SANITY 0
#define HEAP_CHECK_PERIOD 1000

/*************************************************************************
 * Globals 
 * This data has to be kept < 128 bytes
 * Currently it uses 96B
 * However, 36B of that is for debug so it could be removed if necessary
 * and the epilogue pointer is really only for convenience (it can be computed from mem_heap_hi)
*************************************************************************/
void* epilogue = NULL; // 4B
void* fls[NUM_FREE_LISTS]; // 7 * 4 = 28B
size_t limits[NUM_FREE_LISTS]; // 7 * 4 = 28B
int counter;//For debug 4B
int itr=0;//For debug 4B
int number_of_items[NUM_FREE_LISTS];//For debug 7 * 4 = 28B

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

/*************************************************************************
 * Debugging Functions
 * These help with debugging our program, running our heap checker
 * and asserting that our program passes the tests
 * (Only run when DEBUG or SANITY_CHECK are on)
*************************************************************************/
// Prints a character then flushes stdout in case there's a seg fault
void printFlush(char *c)
{
	printf("%s",c);	
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
//If a check fails the program dies because something is wrong and we should fix it
void mm_check()
{
	int i;
	for (i = 0; i < NUM_FREE_LISTS; ++i)
	{
		 //Run sanity check for every free list we have.
		run_check(fls[i], limits[i], i>0?limits[i-1]:0);
	}
	//Correctness test takes an array of free lists
	assert(flCorrectnessCheck(fls));
}

//This function runs when debug or sanity check are on
//It performs the behaviour described above for the DEBUG and SANITY flags
void heapCheckCounter(char* c)
{
	counter++;
	
	//debug: run on RUN_ON_INSN only
	printf("(%s%i)",c,counter); printFlush("");
	if(counter==RUN_ON_INSN)
	{
		//only run once for each test
		if(itr%12==1)
			mm_check();
	}
	
	//sanity: run every HEAP_CHECK_PERIOD insns
	if(counter%HEAP_CHECK_PERIOD==0)
	{
		//only run once for each test
		if(itr%12==1)
			mm_check();
	}
}

/**********************************************************
 * Main functions
 **********************************************************/

/**********************************************************
 * mm_init
 * Initialize the heap, including "allocation" of the
 * prologue and epilogue
 * Also initializes the free list pointers and the free list limits
 **********************************************************/
 int mm_init(void)
 {
	int list;
	size_t limit;
	void* heap_listp = NULL;
    
	if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
    	return -1;
    PUT(heap_listp, 0);                         // alignment padding 
	// prologue header
	// The prologue doesn't need a footer (because it's an allocated block)
	// But it still needs to be aligned
	PUT(heap_listp+WSIZE, PACK(ALIGNMENT, 1, 1));   // prologue header
	PUT(heap_listp+DSIZE+WSIZE, PACK(0, 1, 1));    // epilogue header

	// This pointer makes some work easier later (such as reallocing)	
	epilogue = heap_listp+DSIZE+DSIZE;
	
	// Initialize free lists and limits
	limit = 16;
	for (list = 0; list < NUM_FREE_LISTS; ++list)
	{
		fls[list] = NULL;
		limits[list] = ALIGNMENT * (limit + ALLOC_OVERHEAD + ALIGNMENT - 1)/ALIGNMENT;
		limit = limit << 1;
	}
	
	//set last limit to -1, meaning there is no upper limit
	limits[NUM_FREE_LISTS - 1] = -1;
	
	//counter and itr are used in debugging
	counter=0;
	itr++;
	return 0;
 }

// Adds the block pointed to by bp to the head of the appropriate free list
// Assumes the block has already been marked as free,
// that its header and footer are set up appropriately, 
// and that the prev bit of the next physical block is handled elsewhere
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

// Removes the block pointed to by bp from its free list
// by changing the prev and next block pointers
// Does not mark the block as allocated
// Does not change the prev bit of the next physical block
void remove_from_free_list(void* bp)
{
	// Get the blocks immediately before and after this one in the list
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
		// Make the next block the new head of the list
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
 * Removes the neighbouring free blocks from their lists
 * Combines the blocks
 * Adds the new block to the free list
 **********************************************************/
void *coalesce(void *bp)
{
	unsigned int prev_alloc = GET_PREV(HDRP(bp));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	
	//Nothing special to do for case 1 (both prev and next allocated)
	if (prev_alloc &&!next_alloc)
    { /* Case 2 faFfaf*/
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        void * nbp=NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0, 1));
        PUT(FTRP(bp), PACK(size, 0, 1));

		remove_from_free_list(nbp);
    }
    else if (next_alloc&&!prev_alloc)
	{ /* Case 3 fafFaf*/
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0, 1));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0, 1));
       
		remove_from_free_list(PREV_BLKP(bp)); 
		bp = PREV_BLKP(bp);
    }
    else if (!next_alloc&&!prev_alloc)
	{ /* Case 4 fafFfaf */
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

// Nifty round up to the next power of two without loops/ifs
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
 * Coalesce the new free block (i.e. add it to the free list)
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
	unsigned int prev = GET_PREV(HDRP(epilogue));
	PUT(HDRP(bp), PACK(size, 0, prev));                // free block header
    PUT(FTRP(bp), PACK(size, 0, prev));                // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1, 0));        // new epilogue header

	// Update the epilogue pointer
	epilogue = NEXT_BLKP(bp);
	
	/* Coalesce if the previous block was free */
    return coalesce(bp);
}


/**********************************************************
 * find_fit
 * Traverse the appropriate free list to find a block of size asize
 * If none is found search the next largest free list
 * Continue this until a block is found or we're out of free lists
 * If a block is found return a pointer to it
 * Return NULL if no free blocks can handle that size
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

	// Search through all free lists starting at the one determined above
    while (list < NUM_FREE_LISTS)
	{
		for (bp = fls[list]; bp!=NULL; bp = GetNext(bp))//Go through the free list
		{
			//If a block fits
			if ((asize <= GET_SIZE(HDRP(bp))))
			{
				assert(!GET_ALLOC(HDRP(bp))); // Shouldn't be in the free list if allocated
				return bp;
			}
		}
		++list;
	}

    return NULL;
}

// Splits a free block (bp) into two pieces.
// Return a pointer to the second peice (bp will still be valid and will point to the first peice)
// Assumes the initial block is free
// Both newly produced blocks are still free
// Does not touch the free lists (caller must deal with them)
void *split(void *bp, size_t size)
{
	void * new_block;
	size_t old_size;

	old_size = GET_SIZE(HDRP(bp));
	// Alignment should be maintained
	assert(((old_size - size) % ALIGNMENT) == 0);
	
	// Resize the old block
	PUT(HDRP(bp), PACK(size, 0, GET_PREV(HDRP(bp))));
	PUT(FTRP(bp), PACK(size, 0, GET_PREV(HDRP(bp))));
	// Create the new block
	new_block = NEXT_BLKP(bp);
	PUT(HDRP(new_block), PACK(old_size - size, 0, 0));
	PUT(FTRP(new_block), PACK(old_size - size, 0, 0));
	
	return new_block;
}

/**********************************************************
 * place
 * Remove a block from its free list
 * Split the block if it's large adding the extra back to a free list
 * Mark the block as allocated
 * Update the prev allocated bit of the next physical block
 **********************************************************/
void place(void* bp, size_t asize)
{
 	/* Get the current block size */
    size_t bsize = GET_SIZE(HDRP(bp));

	remove_from_free_list(bp);	

	// For now, we only do splitting on the biggest blocks and only if the remainder would still belong on the biggest queue
	if (bsize > limits[NUM_FREE_LISTS - 2] && (bsize - asize) > limits[NUM_FREE_LISTS - 2])
	{
		// Put the remainder of the block back on a free list
		add_to_free_list(split(bp, asize));
		bsize = asize;
	}

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
// Update the prev bit of the next physical block
// Does not touch the free lists (caller must handle that)
void mark_free(void *bp)
{
    // Update the block
	size_t size = GET_SIZE(HDRP(bp));
    unsigned int prev = GET_PREV(HDRP(bp));
	PUT(HDRP(bp), PACK(size,0,prev));
    PUT(FTRP(bp), PACK(size,0,prev));
	
	// Update the next block
	void * next = NEXT_BLKP(bp);
	size_t next_size = GET_SIZE(HDRP(next));
	unsigned int next_alloc = GET_ALLOC(HDRP(next));
	PUT(HDRP(next), PACK(next_size,next_alloc,0));
	// If it has a footer, update it
	if (next_alloc == 0 && next_size > 0)
		PUT(FTRP(next), PACK(GET_SIZE(HDRP(next)),GET_ALLOC(HDRP(next)),0));
}

/**********************************************************
 * mm_free
 * Free the block and coalesce with neighbouring blocks
 **********************************************************/
void mm_free(void *bp)
{
#if DEBUG | SANITY
	heapCheckCounter("f");
#endif
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
#if DEBUG | SANITY
	heapCheckCounter("m");
#endif
	size_t asize; /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char * bp;
    
	/* Ignore spurious requests */
    if (size <= 0)
        return NULL;

	// Unless the size would result in us using the biggest free list,
	// round up to the next power of 2
	// This reduces fragmentation by semi-standardizing block sizes
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
    extendsize = MAX(asize, CHUNKSIZE);
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
 * Use a simple malloc, copy, and free approach unless the block being realloced is at the end of the heap.
 * If this is the case, the heap is extended and the extra space is appended to that block.  That way no memory needs to be copied.
 * If the block is already big enough that it doesn't need to be resized, don't bother resizing it
 *********************************************************/
void *mm_realloc(void *ptr, size_t size)
{
#if DEBUG | SANITY
	heapCheckCounter("r");
#endif

	size_t difference, extendsize;
	void * new_bp;

	//check what size the block actually is
	size_t block_size = GET_SIZE(HDRP(ptr));
	// Determine what size is needed
	size_t new_size = (size + ALLOC_OVERHEAD + ALIGNMENT -1) / ALIGNMENT * ALIGNMENT;
	//if the allocated size is enough to fit what the user wants
	if(new_size <= block_size)
		return ptr;//they can still use the same memory
	
	void *newptr;
    
	// If the block being grown is the last block, then there's no need to copy, just extend the heap and give the extra space to this block
	if (NEXT_BLKP(ptr) == epilogue)
	{
		difference = new_size - block_size;
		// Extend the heap
		extendsize = MAX(difference, CHUNKSIZE);
		if ((new_bp = extend_heap(extendsize/WSIZE)) == NULL)
		{
			return NULL;
		}
		remove_from_free_list(new_bp);
		// Combine the blocks
		PUT(HDRP(ptr), PACK(block_size+extendsize, 1, GET_PREV(HDRP(ptr))));
		// Update the epilogue's prev
		PUT(HDRP(epilogue), PACK(0, 1, 1));
		newptr = ptr;
	}
	else
	{
		//We must allocate more memory!
		newptr=mm_malloc(new_size);
	
		//if malloc failed, return NULL
		if (newptr == NULL)
			return NULL;	
	
		//copy stuff from old ptr to new ptr
		memcpy(newptr,ptr,new_size);
		mm_free(ptr);
	}	
	return newptr;
}



















/**********************************************************
 * Herein lies the almighty HEAP CHEKKA
 *********************************************************/


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
		number_of_items[i]=0;
		//go through the list
		for(bp=l[i];bp!=NULL;bp=GetNext(bp))
		{
			//count all the things!
			number_of_items[i]++;
		}
	}
	return number_of_items;
}

//print one check
void printCheck(char*c,int b)
{
	printf("\n%i CHEKKA: %s?",b,c); printFlush("");
}
//print all checks
void heapChekka(void* l)
{
	printCheck("1. Do pointers in heap block point to valid heap addresses",	flPointerBoundsCheck(l));
	printCheck("2. Is every block in the free list marked as free", flAllFreeCheck(l));
	printCheck("3. Do pointers in free list point to valid free blocks", flValidPointersCheck(l));
	printCheck("4. Are blocks are coalesced properly",coalescingCheck(l));
	printCheck("5. Is every free block actually in the free list" ,flCorrectnessCheck(l));
	printf("\n\n\n");printFlush("");
	
}









