// splay.h
// interface to malloc annotated with splay tree info
// for fast indexing by pointer

#ifndef SPLAY_H
#define SPLAY_H

// hack: since ccured.h gets effectively included twice due
// to the way we do preprocessing, I'll avoid including
// any system headers
//#include <stdlib.h>      // size_t

#ifdef __cplusplus
extern "C" {
#endif

// ----------- mutators -----------
// returns a new block of memory, indexed in the tree
void *splayMalloc(unsigned int size);

// free such a block
void splayFree(void *block);

// remove a block from the tree, but don't actually
// call 'free'
void splayRemoveBlock(void *block);

// realloc: change size of block
void *splayRealloc(void *oldBlock, unsigned int newSize);

// calloc: allocate size bytes, init'd to 0
void *splayMallocZeroed(unsigned int size);


// actions for tree walker
enum SplayWalkOpts {
  SW_GO    = 0,      // keep going
  SW_STOP  = 1,      // stop iterating (not implemented)
  SW_FREE  = 2,      // free the block just examined
};

// user-supplied per-block function
typedef enum SplayWalkOpts (*SplayWalkFn)(void *block);

// splay walk entry
void splayWalkTree(SplayWalkFn func);


// ------------ queries -------------
// given a pointer to a block (possibly to its interior),
// find the head of that block (i.e. the value that
// splayMalloc returned), or NULL if it's not a valid pointer
void *findSplayBlock(void *interiorPointer);

// verify that 'block' is a valid block (i.e. it was the
// return value of splayMalloc, and hasn't been deallocated);
// this fails an assertion if it's not a valid block
void validateBlock(void *block);

// get the size of a block, given a pointer to its head, which
// must be valid
unsigned int getSplayBlockSize(void *block);

// print a tree representation to stdout
void printSplayTree();

// given a block pointer as yielded during iteration of
// 'walkMallocHeap', map it into a splay block pointer
void *mallocBlockToSplayBlock(void *mallocBlock);

// tell me which global addresses to *not* trace during gc
// (end is last+1)
void getSplayExcludedRoots(void **start, void **end);


// ------------- garbage collector (splaygc.c) -----------
// garbage collect; return # of freed block
int sgcGarbageCollect();

// mark a block as programmer-freed; reclaim the storage
// once we can prove no further accesses are possible
void sgcMaybeFree(void *block);


// -------------------- interval interface --------------------------
/* Do not change these tags without changing box.ml */
// we distinguish three kinds of surrounding metadata
enum registerAreaKind {
  registerTagged = 0, // base is the base of a tagged area
  registerSized  = 1, // base is the base of a sized array
  registerSeq    = 2, // base is the base of an array. end is the byte after
                      // the array

  numAreaKinds
};


// we distinguish three memory regions: stack, globals, and heap
enum MemRegion {
  MR_STACK=0,
  MR_GLOBAL=1,
  MR_HEAP=2,
  NUM_MEMREGIONS
};


// print to stdout the splay tree for the given region and kind
void splayPrintTreeKind(enum MemRegion mr, int kind);

// find the base of a home area for a given (possibly) interior
// pointer, of a given kind; if the pointer is not to a valid
// interval, returns NULL
void *splayFindHome(int kind, void *interiorPointer);

// same as 'splayFindHome', but also return the 'end' pointer
void *splayFindHomeEnd(int kind, void *ptr, void **end);

// remove all nodes below the given cutoff address
void splayRemoveKindBelow(enum MemRegion mr, int kind, void *cutoffAddr);

// insert a new interval into the given tree
void splayInsertInterval(int kind, void *base, unsigned length);




#ifdef __cplusplus
}
#endif

#endif // SPLAY_H
