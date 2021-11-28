#include <stdlib.h>
#include <string.h>

#include "memory.h"

static void acquireLockSignalGc(MochiVM* vm) {
    int lockRes = mtx_trylock(&vm->allocLock);
    while (lockRes != thrd_success) {
        PANIC_IF(lockRes == thrd_error, "Failed to acquire lock in an allocation.");
        ObjFiber* fiber = mochiThreadCurrent(vm);
        while (vm->collecting) {
            fiber->isPausedForGc = true;
        }
        fiber->isPausedForGc = false;
        lockRes = mtx_trylock(&vm->allocLock);
    }
}

void* mochiReallocate(MochiVM* vm, void* memory, size_t oldSize, size_t newSize) {

    // TODO: while this method is protected from starting multiple GC cycles simultaneously
    // thanks to a simple lock, it is not yet fully thread safe with respect to moving around
    // data. Need thread synchronization before declaring multithread safe GC!

    // Only lock if we're allocating new memory, since that's the only thing that
    // will prompt a new GC cycle.
    if (newSize > 0) {
        acquireLockSignalGc(vm);
#if MOCHIVM_DEBUG_TRACE_MEMORY
        printf("Lock acquired.\n");
#endif
    }

    // If new bytes are being allocated, add them to the total count. If objects
    // are being completely deallocated, we don't track that (since we don't
    // track the original size). Instead, that will be handled while marking
    // during the next GC.
    size_t newHeapSize = vm->bytesAllocated + (newSize - oldSize);

#if MOCHIVM_DEBUG_TRACE_MEMORY
    // Explicit cast because size_t has different sizes on 32-bit and 64-bit and
    // we need a consistent type for the format string.
    printf("reallocate %p %lu -> %lu, total %lu -> %lu\n", memory, (unsigned long)oldSize, (unsigned long)newSize,
           (unsigned long)vm->bytesAllocated, (unsigned long)newHeapSize);
#endif

    vm->bytesAllocated = newHeapSize;

#if MOCHIVM_DEBUG_GC_STRESS
    // Since collecting calls this function to free things, make sure we don't
    // recurse.
    bool shouldGc = newSize > 0 && mochiThreadCount(vm) > 0;
#else
    bool shouldGc = newSize > 0 && newHeapSize > vm->nextGC && mochiThreadCount(vm) > 0;
#endif
    if (shouldGc) {
        ObjFiber* current = mochiThreadCurrent(vm);
        current->isPausedForGc = true;
        mochiCollectGarbage(vm);
        current->isPausedForGc = false;
    }

    void* res = vm->config.reallocateFn(memory, newSize, vm->config.userData);

    if (newSize > 0) {
        if (mtx_unlock(&vm->allocLock) == thrd_success) {
#if MOCHIVM_DEBUG_TRACE_MEMORY
            printf("Lock released.\n");
#endif
        } else {
            PANIC("Could not free the lock during allocation.");
        }
    }

    return res;
}

// From: http://graphics.stanford.edu/~seander/bithacks.html#RoundUpPowerOf2Float
int mochiPowerOf2Ceil(int n) {
    n--;
    n |= n >> 1;
    n |= n >> 2;
    n |= n >> 4;
    n |= n >> 8;
    n |= n >> 16;
    n++;
    return n;
}