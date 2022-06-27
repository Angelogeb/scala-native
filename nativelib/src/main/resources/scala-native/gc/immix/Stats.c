#include "Stats.h"
#include <stdio.h>
#include <inttypes.h>

void Stats_writeToFile(Stats *stats);

void Stats_Init(Stats *stats, const char *statsFile) {
    stats->outFile = fopen(statsFile, "w");
    fprintf(stats->outFile, "mark_time_ns,sweep_time_ns,n_large_heap_allocs,n_small_heap_allocs,n_shstack_allocs,shstack_peak\n");
    stats->collections = 0;
}

uint64_t large_heap_allocs = 0;
uint64_t small_heap_allocs = 0;
uint64_t shstack_allocs = 0;
uint64_t shstack_peak = 0;

void Stats_RecordCollection(Stats *stats, uint64_t start_ns,
                            uint64_t sweep_start_ns, uint64_t end_ns) {
    uint64_t index = stats->collections % STATS_MEASUREMENTS;
    stats->mark_time_ns[index] = sweep_start_ns - start_ns;
    stats->sweep_time_ns[index] = end_ns - sweep_start_ns;
    stats->large_heap_allocs[index] = large_heap_allocs;
    stats->small_heap_allocs[index] = small_heap_allocs;
    stats->shstack_allocs[index] = shstack_allocs;
    stats->shstack_peak = shstack_peak;

    large_heap_allocs = 0;
    small_heap_allocs = 0;
    shstack_allocs = 0;
    shstack_peak = 0;

    stats->collections += 1;
    if (stats->collections % STATS_MEASUREMENTS == 0) {
        Stats_writeToFile(stats);
    }
}

void Stats_writeToFile(Stats *stats) {
    uint64_t collections = stats->collections;
    uint64_t remainder = collections % STATS_MEASUREMENTS;
    if (remainder == 0) {
        remainder = STATS_MEASUREMENTS;
    }
    FILE *outFile = stats->outFile;
    for (uint64_t i = 0; i < remainder; i++) {
        fprintf(outFile, "%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 "\n", stats->mark_time_ns[i],
                stats->sweep_time_ns[i], stats->large_heap_allocs[i], stats->small_heap_allocs[i], stats->shstack_allocs[i], stats->shstack_peak);
    }
    fflush(outFile);
}

void Stats_OnExit(Stats *stats) {
    if (stats != NULL) {
        uint64_t remainder = stats->collections % STATS_MEASUREMENTS;
        if (remainder > 0) {
            // there were some measurements not written in the last full batch.
            Stats_writeToFile(stats);
        }
        fclose(stats->outFile);
    }
}