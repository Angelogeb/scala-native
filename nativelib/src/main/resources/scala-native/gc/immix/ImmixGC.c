#include <stdio.h>
#include <stdlib.h>
#include <memory.h>
#include "GCTypes.h"
#include "Heap.h"
#include "datastructures/Stack.h"
#include "Marker.h"
#include "Log.h"
#include "Object.h"
#include "State.h"
#include "utils/MathUtils.h"
#include "Constants.h"
#include "Settings.h"
#include "Stats.h"


//////////////////////
#include <sys/mman.h>

#define MB(x) ((x) * 1024 * 1024L)
#define LOCAL_CHUNK (MB(1000))

#define INLINE __attribute__((always_inline))
#define LOCALALLOC_DEBUG (0)


void scalanative_local_init() {
    local_start = mmap(NULL, LOCAL_CHUNK, (PROT_READ | PROT_WRITE), (MAP_NORESERVE | MAP_PRIVATE | MAP_ANONYMOUS), -1,
                   0);
    local_current = local_start;
    local_frameptr = local_current;
    local_end = local_current + LOCAL_CHUNK;

    word_t** tmp_start = local_start;

    for (word_t** cursor = local_start; cursor < tmp_start + MB(1); cursor += 1) {
      *cursor = NULL;
    }

    if (LOCALALLOC_DEBUG) {
      fprintf(stderr, "[init] local_current: %p, local_end: %p\n", local_current, local_end);
      fflush(stderr);
    }
}


INLINE void* scalanative_localalloc(void *info, size_t size) {
    shstack_allocs += 1;
    size = size + (8 - size % 8);
    if (local_current + size >= local_end) {
      fprintf(stderr, "Local allocation exceeds maximum size of %fMB \n", LOCAL_CHUNK / (double) MB(1));
      return NULL;
    }
    void **alloc = local_current;
    *alloc = info;
    local_current += size;
    shstack_peak = (local_current - local_start) > shstack_peak? (local_current - local_start) : shstack_peak;
    if (LOCALALLOC_DEBUG) {
      fprintf(stderr, "[local_alloc] local_current: %p\n", local_current);
      fflush(stderr);
    }

    return alloc;
}

//When a first class function is entered
INLINE void scalanative_local_enter1() {
  size_t size = sizeof(void *);
  void **alloc = local_current;
  *alloc = local_frameptr;
  local_frameptr = local_current;
  local_current += size;
  if (LOCALALLOC_DEBUG) {
    fprintf(stderr, "[enter1] local_current: %p\n", local_current);
    fflush(stderr);
  }
}

// When a first class function returns
INLINE void scalanative_local_exit1() {
  void** parent_frameptrptr = local_frameptr;
  if (local_frameptr != NULL) {
    local_current = local_frameptr;
    local_frameptr = *parent_frameptrptr;
    if (LOCALALLOC_DEBUG) {
      fprintf(stderr, "[exit1] local_current: %p\n", local_current);
      fflush(stderr);
    }
  } else {
    fprintf(stderr, "WARNGING: Local exit on NULL pointer");
  }
}
//////////////////////

void scalanative_collect();

void scalanative_afterexit() { Stats_OnExit(heap.stats); }

NOINLINE void scalanative_init() {
    Heap_Init(&heap, Settings_MinHeapSize(), Settings_MaxHeapSize());
    Stack_Init(&stack, INITIAL_STACK_SIZE);
    scalanative_local_init();
    atexit(scalanative_afterexit);
}

INLINE void *scalanative_alloc(void *info, size_t size) {
    size = MathUtils_RoundToNextMultiple(size, ALLOCATION_ALIGNMENT);

    void **alloc = (void **)Heap_Alloc(&heap, size);
    *alloc = info;
    return (void *)alloc;
}

INLINE void *scalanative_alloc_small(void *info, size_t size) {
    size = MathUtils_RoundToNextMultiple(size, ALLOCATION_ALIGNMENT);

    void **alloc = (void **)Heap_AllocSmall(&heap, size);
    *alloc = info;
    return (void *)alloc;
}

INLINE void *scalanative_alloc_large(void *info, size_t size) {
    size = MathUtils_RoundToNextMultiple(size, ALLOCATION_ALIGNMENT);

    void **alloc = (void **)Heap_AllocLarge(&heap, size);
    *alloc = info;
    return (void *)alloc;
}

INLINE void *scalanative_alloc_atomic(void *info, size_t size) {
    return scalanative_alloc(info, size);
}

INLINE void scalanative_collect() { Heap_Collect(&heap, &stack); }
