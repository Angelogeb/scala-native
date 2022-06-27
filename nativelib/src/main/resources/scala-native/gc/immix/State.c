#include "State.h"

Heap heap;
Stack stack;
Allocator allocator;
LargeAllocator largeAllocator;
BlockAllocator blockAllocator;

void *local_start = 0;
void *local_current = 0;
void *local_end = 0;
void *local_frameptr = 0;