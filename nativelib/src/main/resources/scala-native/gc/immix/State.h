#ifndef IMMIX_STATE_H
#define IMMIX_STATE_H

#include "Heap.h"

extern Heap heap;
extern Stack stack;
extern Allocator allocator;
extern LargeAllocator largeAllocator;
extern BlockAllocator blockAllocator;

extern void *local_start;
extern void *local_current;
extern void *local_end;
extern void *local_frameptr;

#endif // IMMIX_STATE_H
