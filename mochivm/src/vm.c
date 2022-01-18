#include <stdio.h>
#include <string.h>

#include "common.h"
#include "debug.h"
#include "memory.h"
#include "vm.h"

#if MOCHIVM_DEBUG_TRACE_MEMORY || MOCHIVM_DEBUG_TRACE_GC
#include <time.h>
#endif

#if MOCHIVM_BATTERY_UV
#include "battery_uv.h"
#include "uv.h"
#endif

#if MOCHIVM_BATTERY_SDL
#include "battery_sdl.h"
#endif

DEFINE_BUFFER(ForeignFunction, MochiVMForeignMethodFn);
DEFINE_BUFFER(Fiber, ObjFiber*);

// The behavior of realloc() when the size is 0 is implementation defined. It
// may return a non-NULL pointer which must not be dereferenced but nevertheless
// should be freed. To prevent that, we avoid calling realloc() with a zero
// size.
static void* defaultReallocate(void* ptr, size_t newSize, void* _) {
    if (newSize == 0) {
        free(ptr);
        return NULL;
    }
    return realloc(ptr, newSize);
}

#if MOCHIVM_BATTERY_UV
static void* uvmochiMalloc(size_t size) {
    return defaultReallocate(NULL, size, NULL);
}
static void* uvmochiRealloc(void* ptr, size_t size) {
    return defaultReallocate(ptr, size, NULL);
}
static void* uvmochiCalloc(size_t count, size_t size) {
    void* mem = defaultReallocate(NULL, count * size, NULL);
    memset(mem, 0, count * size);
    return mem;
}
static void uvmochiFree(void* ptr) {
    defaultReallocate(NULL, 0, NULL);
}
#endif

int mochiGetVersionNumber() {
    return MOCHIVM_VERSION_NUMBER;
}

void mochiInitConfiguration(MochiVMConfiguration* config) {
    config->reallocateFn = defaultReallocate;
    config->errorFn = NULL;
    config->valueStackCapacity = 128;
    config->frameStackCapacity = 512;
    config->rootStackCapacity = 16;
    config->initialHeapSize = 1024 * 1024 * 10;
    config->minHeapSize = 1024 * 1024;
    config->heapGrowthPercent = 50;
    config->userData = NULL;
}

MochiVM* mochiNewVM(MochiVMConfiguration* config) {
    MochiVMReallocateFn reallocate = defaultReallocate;
    void* userData = NULL;
    if (config != NULL) {
        userData = config->userData;
        reallocate = config->reallocateFn ? config->reallocateFn : defaultReallocate;
    }

    MochiVM* vm = (MochiVM*)reallocate(NULL, sizeof(*vm), userData);
    memset(vm, 0, sizeof(MochiVM));

    // Copy the configuration if given one.
    if (config != NULL) {
        memcpy(&vm->config, config, sizeof(MochiVMConfiguration));

        // We choose to set this after copying,
        // rather than modifying the user config pointer
        vm->config.reallocateFn = reallocate;
    } else {
        mochiInitConfiguration(&vm->config);
    }

    vm->grayCount = 0;
    // TODO: Tune this.
    vm->grayCapacity = 4;
    vm->gray = (Obj**)reallocate(NULL, vm->grayCapacity * sizeof(Obj*), userData);
    vm->nextGC = vm->config.initialHeapSize;

    mtx_init(&vm->allocLock, mtx_plain);

    mochiByteBufferInit(&vm->code);
    mochiIntBufferInit(&vm->lines);
    mochiValueBufferInit(&vm->constants);
    mochiIntBufferInit(&vm->labelIndices);
    mochiValueBufferInit(&vm->labels);
    mochiForeignFunctionBufferInit(&vm->foreignFns);
    mochiFiberBufferInit(&vm->fibers);
    mochiTableInit(&vm->heap);
    // start at 2 since 0 and 1 are reserved for available/tombstoned slots
    vm->nextHeapKey = 2;

#if MOCHIVM_BATTERY_UV
    uv_replace_allocator(uvmochiMalloc, uvmochiRealloc, uvmochiCalloc, uvmochiFree);

    mochiAddForeign(vm, uvmochiNewTimer);
    mochiAddForeign(vm, uvmochiCloseTimer);
    mochiAddForeign(vm, uvmochiTimerStart);
#endif

#if MOCHIVM_BATTERY_SDL
    mochiAddForeign(vm, sdlmochiInit);
    mochiAddForeign(vm, sdlmochiQuit);
#endif

    return vm;
}

void mochiFreeVM(MochiVM* vm) {

    // Free all of the GC objects.
    Obj* obj = vm->objects;
    while (obj != NULL) {
        Obj* next = obj->next;
        mochiFreeObj(vm, obj);
        obj = next;
    }

    // Free up the GC gray set.
    vm->gray = (Obj**)vm->config.reallocateFn(vm->gray, 0, vm->config.userData);

    mochiByteBufferClear(vm, &vm->code);
    mochiIntBufferClear(vm, &vm->lines);
    mochiValueBufferClear(vm, &vm->constants);
    mochiIntBufferClear(vm, &vm->labelIndices);
    mochiValueBufferClear(vm, &vm->labels);
    mochiForeignFunctionBufferClear(vm, &vm->foreignFns);
    mochiFiberBufferClear(vm, &vm->fibers);
    mochiTableClear(vm, &vm->heap);

    mtx_destroy(&vm->allocLock);
    DEALLOCATE(vm, vm);
}

bool mochiHasPermission(MochiVM* vm, int permissionId) {
    ASSERT(false, "Permission querying not yet implemented.");
    return false;
}

bool mochiRequestPermission(MochiVM* vm, int permissionId) {
    ASSERT(false, "Permission requesting not yet implemented.");
    return false;
}

bool mochiRequestAllPermissions(MochiVM* vm, int permissionId) {
    ASSERT(false, "Permission requesting not yet implemented.");
    return false;
}

void mochiRevokePermission(MochiVM* vm, int permissionId) {
    ASSERT(false, "Permission revoking not yet implemented.");
}

static void waitForThreadSync(MochiVM* vm) {
    bool allThreadsPaused = false;
    while (!allThreadsPaused) {
        allThreadsPaused = true;
        for (int i = 0; i < vm->fibers.count; i++) {
            // fibers will set their ready for gc flags when they've reached a safe point
            allThreadsPaused = allThreadsPaused && vm->fibers.data[i] != NULL && vm->fibers.data[i]->isPausedForGc;
        }
    }
}

static void sweep(MochiVM* vm, unsigned long* freed, unsigned long* reachable) {

    Obj** obj = &vm->objects;
    while (*obj != NULL) {
        if (!((*obj)->isMarked)) {
            // This object wasn't reached, so remove it from the list and free it.
            Obj* unreached = *obj;
            *obj = unreached->next;
            mochiFreeObj(vm, unreached);
            *freed += 1;
        } else {
            // This object was reached, so unmark it (for the next GC) and move on to
            // the next.
            (*obj)->isMarked = false;
            obj = &(*obj)->next;
            *reachable += 1;
        }
    }
}

void mochiCollectGarbage(MochiVM* vm) {
    vm->collecting = true;

#if MOCHIVM_DEBUG_TRACE_MEMORY || MOCHIVM_DEBUG_TRACE_GC
    printf("-- gc --\n");

    size_t before = vm->bytesAllocated;
    double startTime = (double)clock() / CLOCKS_PER_SEC;
#endif

    waitForThreadSync(vm);

#if MOCHIVM_DEBUG_TRACE_MEMORY || MOCHIVM_DEBUG_TRACE_GC
    double paused = ((double)clock() / CLOCKS_PER_SEC) - startTime;
    printf("Took %.3fms to pause all threads for GC.", paused * 1000.0);
#endif

    // Mark all reachable objects.

    // Reset this. As we mark objects, their size will be counted again so that
    // we can track how much memory is in use without needing to know the size
    // of each *freed* object.
    //
    // This is important because when freeing an unmarked object, we don't always
    // know how much memory it is using. For example, when freeing an instance,
    // we need to know its class to know how big it is, but its class may have
    // already been freed.
    vm->bytesAllocated = 0;

    mochiGrayBuffer(vm, &vm->constants);
    mochiGrayBuffer(vm, &vm->labels);
    for (int i = 0; i < vm->fibers.count; i++) {
        mochiGrayObj(vm, (Obj*)vm->fibers.data[i]);
    }

    // Now that we have grayed the roots, do a depth-first search over all of the
    // reachable objects.
    mochiBlackenObjects(vm);

    // Collect the white objects.
    unsigned long freed = 0;
    unsigned long reachable = 0;
    sweep(vm, &freed, &reachable);

    // Calculate the next gc point, this is the current allocation plus
    // a configured percentage of the current allocation.
    vm->nextGC = vm->bytesAllocated + ((vm->bytesAllocated * vm->config.heapGrowthPercent) / 100);
    if (vm->nextGC < vm->config.minHeapSize)
        vm->nextGC = vm->config.minHeapSize;

#if MOCHIVM_DEBUG_TRACE_MEMORY || MOCHIVM_DEBUG_TRACE_GC
    double elapsed = ((double)clock() / CLOCKS_PER_SEC) - startTime;
    // Explicit cast because size_t has different sizes on 32-bit and 64-bit and
    // we need a consistent type for the format string.
    printf("GC %lu reachable, %lu freed. Took %.3fms.\nGC %lu before, %lu after (~%lu collected), next at %lu.\n",
           reachable, freed, elapsed * 1000.0, (unsigned long)before, (unsigned long)vm->bytesAllocated,
           (unsigned long)(before - vm->bytesAllocated), (unsigned long)vm->nextGC);
#endif

    // Notify threads that they may unpause themselves.
    vm->collecting = false;
}

int mochiWriteCodeI8(MochiVM* vm, int8_t val, int line) {
    uint8_t reint;
    memcpy(&reint, &val, 1);
    return mochiWriteCodeByte(vm, val, line);
}

int mochiWriteCodeByte(MochiVM* vm, uint8_t instr, int line) {
    mochiByteBufferWrite(vm, &vm->code, instr);
    mochiIntBufferWrite(vm, &vm->lines, line);
    return vm->code.count - 1;
}

int mochiWriteCodeI16(MochiVM* vm, int16_t val, int line) {
    mochiWriteCodeByte(vm, (val) >> 8, (line));
    mochiWriteCodeByte(vm, (val), (line));
    return vm->code.count - 1;
}

int mochiWriteCodeU16(MochiVM* vm, uint16_t val, int line) {
    mochiWriteCodeByte(vm, (val) >> 8, (line));
    mochiWriteCodeByte(vm, (val), (line));
    return vm->code.count - 1;
}

int mochiWriteCodeI32(MochiVM* vm, int32_t val, int line) {
    mochiWriteCodeByte(vm, (val) >> 24, (line));
    mochiWriteCodeByte(vm, (val) >> 16, (line));
    mochiWriteCodeByte(vm, (val) >> 8, (line));
    mochiWriteCodeByte(vm, (val), (line));
    return vm->code.count - 1;
}

int mochiWriteCodeU32(MochiVM* vm, uint32_t val, int line) {
    mochiWriteCodeByte(vm, (val) >> 24, (line));
    mochiWriteCodeByte(vm, (val) >> 16, (line));
    mochiWriteCodeByte(vm, (val) >> 8, (line));
    mochiWriteCodeByte(vm, (val), (line));
    return vm->code.count - 1;
}

int mochiWriteCodeI64(MochiVM* vm, int64_t val, int line) {
    mochiWriteCodeByte(vm, (val) >> 52, (line));
    mochiWriteCodeByte(vm, (val) >> 48, (line));
    mochiWriteCodeByte(vm, (val) >> 40, (line));
    mochiWriteCodeByte(vm, (val) >> 32, (line));
    mochiWriteCodeByte(vm, (val) >> 24, (line));
    mochiWriteCodeByte(vm, (val) >> 16, (line));
    mochiWriteCodeByte(vm, (val) >> 8, (line));
    mochiWriteCodeByte(vm, (val), (line));
    return vm->code.count - 1;
}

int mochiWriteCodeU64(MochiVM* vm, uint64_t val, int line) {
    mochiWriteCodeByte(vm, (val) >> 52, (line));
    mochiWriteCodeByte(vm, (val) >> 48, (line));
    mochiWriteCodeByte(vm, (val) >> 40, (line));
    mochiWriteCodeByte(vm, (val) >> 32, (line));
    mochiWriteCodeByte(vm, (val) >> 24, (line));
    mochiWriteCodeByte(vm, (val) >> 16, (line));
    mochiWriteCodeByte(vm, (val) >> 8, (line));
    mochiWriteCodeByte(vm, (val), (line));
    return vm->code.count - 1;
}

int mochiWriteCodeSingle(MochiVM* vm, float val, int line) {
    int32_t reint;
    memcpy(&reint, &val, 4);
    return mochiWriteCodeI32(vm, reint, line);
}

int mochiWriteCodeDouble(MochiVM* vm, double val, int line) {
    int64_t reint;
    memcpy(&reint, &val, 8);
    return mochiWriteCodeI64(vm, reint, line);
}

int mochiWriteLabel(MochiVM* vm, int byteIndex, const char* labelText) {
    mochiIntBufferWrite(vm, &vm->labelIndices, byteIndex);
    mochiValueBufferWrite(vm, &vm->labels, OBJ_VAL(NULL));
    ObjByteArray* str = mochiByteArrayString(vm, labelText);
    vm->labels.data[vm->labels.count - 1] = OBJ_VAL(str);
    return vm->labels.count - 1;
}

const char* mochiGetLabel(MochiVM* vm, int byteIndex) {
    for (int i = 0; i < vm->labelIndices.count; i++) {
        if (vm->labelIndices.data[i] == byteIndex) {
            return AS_CSTRING(vm->labels.data[i]);
        }
    }
    return NULL;
}

static int mochiWriteConstant(MochiVM* vm, Value value) {
    mochiValueBufferWrite(vm, &vm->constants, I32_VAL(vm, 0));
    vm->constants.data[vm->constants.count - 1] = value;
    return vm->constants.count - 1;
}

int mochiWriteI32Const(MochiVM* vm, int32_t val) {
    return mochiWriteConstant(vm, I32_VAL(vm, val));
}

int mochiWriteSingleConst(MochiVM* vm, float val) {
    return mochiWriteConstant(vm, SINGLE_VAL(vm, val));
}

int mochiWriteDoubleConst(MochiVM* vm, double val) {
    return mochiWriteConstant(vm, DOUBLE_VAL(vm, val));
}

int mochiWriteStringConst(MochiVM* vm, const char* val) {
    int ind = mochiWriteConstant(vm, I32_VAL(vm, 0));
    ObjByteArray* str = mochiByteArrayString(vm, val);
    vm->constants.data[ind] = OBJ_VAL(str);
    return ind;
}

int mochiWriteObjConst(MochiVM* vm, Obj* val) {
    return mochiWriteConstant(vm, OBJ_VAL(val));
}

int mochiAddForeign(MochiVM* vm, MochiVMForeignMethodFn fn) {
    mochiForeignFunctionBufferWrite(vm, &vm->foreignFns, fn);
    return vm->foreignFns.count - 1;
}

// using this to get around the garbage collector, can allocate one of these
// and it'll never be garbage collected. But, we have to free it ourselves after
// the thread has been started.
struct NewThread {
    MochiVM* vm;
    ObjFiber* fiber;
};

static void addFiberToVM(MochiVM* vm, ObjFiber* fiber) {
    // find where to place the new fiber
    int fibIndex = -1;
    for (int i = 0; i < vm->fibers.count; i++) {
        if (vm->fibers.data[i] == NULL) {
            vm->fibers.data[i] = fiber;
            fibIndex = i;
            break;
        }
    }
    if (fibIndex < 0) {
        // TODO: this buffer write is not yet thread safe!
        // need a lock here around writing and getting the index of the new fiber
        mochiFiberBufferWrite(vm, &vm->fibers, fiber);
        fibIndex = vm->fibers.count - 1;
    }
}

static void removeFiberFromVM(MochiVM* vm, ObjFiber* fiber) {
    for (int i = 0; i < vm->fibers.count - 1; i++) {
        if (vm->fibers.data[i] == fiber) {
            vm->fibers.data[i] = NULL;
            break;
        }
    }
}

static int mochiFiberThread(void* resume) {
    struct NewThread* thread = resume;
    MochiVM* vm = thread->vm;
    ObjFiber* fiber = thread->fiber;
    DEALLOCATE(vm, thread);

    int res = mochiInterpret(vm, fiber);
    removeFiberFromVM(vm, fiber);
    return res;
}

static void startThread(MochiVM* vm, ObjFiber* caller, ObjFiber* new) {
    addFiberToVM(vm, new);
    struct NewThread* threadMeta = ALLOCATE(vm, struct NewThread);
    threadMeta->vm = vm;
    threadMeta->fiber = new;

    // Now that we're all setup, create the new thread
    int threadStatus = thrd_create(&new->thread, mochiFiberThread, threadMeta);
    if (threadStatus != 0) {
        // Thread creation failed, clean up.
        removeFiberFromVM(vm, new);
        DEALLOCATE(vm, threadMeta);
    }
    mochiFiberPushValue(caller, I32_VAL(vm, threadStatus));
}

void mochiSpawnCall(MochiVM* vm, ObjFiber* caller, int codeStart) {
    ObjFiber* fib = mochiNewFiber(vm, vm->code.data + codeStart, NULL, 0);
    fib->caller = caller;
    mochiFiberPushValue(caller, OBJ_VAL(fib));

    startThread(vm, caller, fib);
}

void mochiSpawnCallWith(MochiVM* vm, ObjFiber* caller, int codeStart, int valueConsume) {
    ObjFiber* fib = mochiNewFiber(vm, vm->code.data + codeStart, NULL, 0);
    fib->caller = caller;
    mochiFiberPushValue(caller, OBJ_VAL(fib));

    // going from valueConsume down ensures the order on the new thread is the same as on the calling thread
    for (int i = valueConsume; i > 0; i--) {
        mochiFiberPushValue(fib, mochiFiberPeekValue(caller, i));
    }
    mochiFiberDropValues(caller, valueConsume);

    startThread(vm, caller, fib);
}

void mochiSpawnCopy(MochiVM* vm, ObjFiber* caller) {
    ObjFiber* fib = mochiFiberClone(vm, caller);
    fib->caller = caller;
    mochiFiberPushValue(caller, OBJ_VAL(fib));

    startThread(vm, caller, fib);
}

ObjFiber* mochiThreadCurrent(MochiVM* vm) {
    thrd_t current = thrd_current();
    for (int i = 0; i < vm->fibers.count; i++) {
        if (vm->fibers.data[i] != NULL && thrd_equal(current, vm->fibers.data[i]->thread)) {
            return vm->fibers.data[i];
        }
    }
    PANIC("Current thread is not a MochiVM thread, but tried to be accessed as one.");
    return NULL;
}

size_t mochiThreadCount(MochiVM* vm) {
    size_t count = 0;
    for (int i = 0; i < vm->fibers.count; i++) {
        count += vm->fibers.data[i] == NULL ? 0 : 1;
    }
    return count;
}

void mochiGrayObj(MochiVM* vm, Obj* obj) {
    if (obj == NULL)
        return;

    // Stop if the object is already darkened so we don't get stuck in a cycle.
    if (obj->isMarked)
        return;

    // It's been reached.
    obj->isMarked = true;

    // Add it to the gray list so it can be recursively explored for
    // more marks later.
    if (vm->grayCount >= vm->grayCapacity) {
        vm->grayCapacity = vm->grayCount * 2;
        vm->gray = (Obj**)vm->config.reallocateFn(vm->gray, vm->grayCapacity * sizeof(Obj*), vm->config.userData);
    }

    vm->gray[vm->grayCount++] = obj;
}

void mochiGrayValue(MochiVM* vm, Value value) {
    if (!IS_OBJ(value))
        return;
    mochiGrayObj(vm, AS_OBJ(value));
}

void mochiGrayBuffer(MochiVM* vm, ValueBuffer* buffer) {
    for (int i = 0; i < buffer->count; i++) {
        mochiGrayValue(vm, buffer->data[i]);
    }
}

#define MARK_SIMPLE(vm, type) ((vm)->bytesAllocated += sizeof(type))

static void markVarFrame(MochiVM* vm, ObjVarFrame* frame) {
    for (int i = 0; i < frame->slotCount; i++) {
        mochiGrayValue(vm, frame->slots[i]);
    }

    vm->bytesAllocated += sizeof(ObjVarFrame);
    vm->bytesAllocated += sizeof(Value) * frame->slotCount;
}

static void markCallFrame(MochiVM* vm, ObjCallFrame* frame) {
    for (int i = 0; i < frame->vars.slotCount; i++) {
        mochiGrayValue(vm, frame->vars.slots[i]);
    }

    vm->bytesAllocated += sizeof(ObjCallFrame);
    vm->bytesAllocated += sizeof(Value) * frame->vars.slotCount;
}

static void markHandleFrame(MochiVM* vm, ObjHandleFrame* frame) {
    for (int i = 0; i < frame->call.vars.slotCount; i++) {
        mochiGrayValue(vm, frame->call.vars.slots[i]);
    }

    mochiGrayObj(vm, (Obj*)frame->afterClosure);
    for (int i = 0; i < frame->handlerCount; i++) {
        mochiGrayObj(vm, (Obj*)frame->handlers[i]);
    }

    vm->bytesAllocated += sizeof(ObjHandleFrame);
    vm->bytesAllocated += sizeof(Value) * frame->call.vars.slotCount;
    vm->bytesAllocated += sizeof(ObjClosure*) * frame->handlerCount;
}

static void markClosure(MochiVM* vm, ObjClosure* closure) {
    for (int i = 0; i < closure->capturedCount; i++) {
        mochiGrayValue(vm, closure->captured[i]);
    }

    vm->bytesAllocated += sizeof(ObjClosure);
    vm->bytesAllocated += sizeof(Value) * closure->capturedCount;
}

static void markContinuation(MochiVM* vm, ObjContinuation* cont) {
    for (int i = 0; i < cont->savedStackCount; i++) {
        mochiGrayValue(vm, cont->savedStack[i]);
    }
    for (int i = 0; i < cont->savedFramesCount; i++) {
        mochiGrayObj(vm, (Obj*)cont->savedFrames[i]);
    }

    vm->bytesAllocated += sizeof(ObjContinuation);
    vm->bytesAllocated += sizeof(Value) * cont->savedStackCount;
    vm->bytesAllocated += sizeof(ObjVarFrame*) * cont->savedFramesCount;
}

static void markFiber(MochiVM* vm, ObjFiber* fiber) {
    // Stack variables.
    for (Value* slot = fiber->valueStack; slot < fiber->valueStackTop; slot++) {
        mochiGrayValue(vm, *slot);
    }

    // Call stack frames.
    for (ObjVarFrame** slot = fiber->frameStack; slot < fiber->frameStackTop; slot++) {
        mochiGrayObj(vm, (Obj*)*slot);
    }

    // Root stack.
    for (Obj** slot = fiber->rootStack; slot < fiber->rootStackTop; slot++) {
        mochiGrayObj(vm, *slot);
    }

    // The caller.
    mochiGrayObj(vm, (Obj*)fiber->caller);

    vm->bytesAllocated += sizeof(ObjFiber);
    vm->bytesAllocated += vm->config.frameStackCapacity * sizeof(ObjVarFrame*);
    vm->bytesAllocated += vm->config.valueStackCapacity * sizeof(Value);
    vm->bytesAllocated += vm->config.rootStackCapacity * sizeof(Obj*);
}

static void markForeign(MochiVM* vm, ObjForeign* foreign) {
    vm->bytesAllocated += sizeof(Obj) + sizeof(int);
    vm->bytesAllocated += sizeof(uint8_t) * foreign->dataCount;
}

static void markList(MochiVM* vm, ObjList* list) {
    mochiGrayValue(vm, list->elem);
    mochiGrayObj(vm, (Obj*)list->next);

    vm->bytesAllocated += sizeof(ObjList);
}

static void markArray(MochiVM* vm, ObjArray* arr) {
    mochiGrayBuffer(vm, &arr->elems);

    vm->bytesAllocated += sizeof(ObjArray);
}

static void markSlice(MochiVM* vm, ObjSlice* slice) {
    mochiGrayObj(vm, (Obj*)slice->source);

    vm->bytesAllocated += sizeof(ObjSlice);
}

static void markByteSlice(MochiVM* vm, ObjByteSlice* slice) {
    mochiGrayObj(vm, (Obj*)slice->source);

    vm->bytesAllocated += sizeof(ObjByteSlice);
}

static void markRef(MochiVM* vm, ObjRef* ref) {
    // TODO: investigate iterating over the table itself to gray set values, determine if performance
    // benefit/degradation
    Value val;
    if (mochiTableGet(&vm->heap, ref->ptr, &val)) {
        mochiGrayValue(vm, val);
    } else {
        ASSERT(false, "Ref does not point to a heap slot.");
    }

    vm->bytesAllocated += sizeof(ObjRef);
}

static void markStruct(MochiVM* vm, ObjStruct* stru) {
    for (int i = 0; i < stru->count; i++) {
        mochiGrayValue(vm, stru->elems[i]);
    }

    vm->bytesAllocated += sizeof(ObjStruct) + stru->count * sizeof(Value);
}

static void markRecord(MochiVM* vm, ObjRecord* rec) {
    for (size_t i = 0; i < rec->count; i++) {
        mochiGrayValue(vm, rec->fields[i].value);
    }

    vm->bytesAllocated += sizeof(ObjRecord);
    vm->bytesAllocated += sizeof(TableEntry) * rec->count;
}

static void markVariant(MochiVM* vm, ObjVariant* var) {
    mochiGrayValue(vm, var->elem);

    vm->bytesAllocated += sizeof(ObjVariant);
}

static void markForeignResume(MochiVM* vm, ForeignResume* resume) {
    mochiGrayObj(vm, (Obj*)resume->fiber);

    vm->bytesAllocated += sizeof(ForeignResume);
}

static void blackenObject(MochiVM* vm, Obj* obj) {
#if ZHEnZHU_DEBUG_TRACE_MEMORY
    printf("mark ");
    printValue(OBJ_VAL(obj));
    printf(" @ %p\n", obj);
#endif

    // Traverse the object's fields.
    switch (obj->type) {
    case OBJ_I64:
        MARK_SIMPLE(vm, ObjI64);
        break;
    case OBJ_U64:
        MARK_SIMPLE(vm, ObjU64);
        break;
    case OBJ_DOUBLE:
        MARK_SIMPLE(vm, ObjDouble);
        break;
    case OBJ_VAR_FRAME:
        markVarFrame(vm, (ObjVarFrame*)obj);
        break;
    case OBJ_CALL_FRAME:
        markCallFrame(vm, (ObjCallFrame*)obj);
        break;
    case OBJ_HANDLE_FRAME:
        markHandleFrame(vm, (ObjHandleFrame*)obj);
        break;
    case OBJ_CLOSURE:
        markClosure(vm, (ObjClosure*)obj);
        break;
    case OBJ_CONTINUATION:
        markContinuation(vm, (ObjContinuation*)obj);
        break;
    case OBJ_FIBER:
        markFiber(vm, (ObjFiber*)obj);
        break;
    case OBJ_FOREIGN:
        markForeign(vm, (ObjForeign*)obj);
        break;
    case OBJ_C_POINTER:
        MARK_SIMPLE(vm, ObjCPointer);
        break;
    case OBJ_LIST:
        markList(vm, (ObjList*)obj);
        break;
    case OBJ_FOREIGN_RESUME:
        markForeignResume(vm, (ForeignResume*)obj);
        break;
    case OBJ_ARRAY:
        markArray(vm, (ObjArray*)obj);
        break;
    case OBJ_BYTE_ARRAY:
        MARK_SIMPLE(vm, ObjByteArray);
        break;
    case OBJ_SLICE:
        markSlice(vm, (ObjSlice*)obj);
        break;
    case OBJ_BYTE_SLICE:
        markByteSlice(vm, (ObjByteSlice*)obj);
        break;
    case OBJ_REF:
        markRef(vm, (ObjRef*)obj);
        break;
    case OBJ_STRUCT:
        markStruct(vm, (ObjStruct*)obj);
        break;
    case OBJ_RECORD:
        markRecord(vm, (ObjRecord*)obj);
        break;
    case OBJ_VARIANT:
        markVariant(vm, (ObjVariant*)obj);
        break;
    }
}

void mochiBlackenObjects(MochiVM* vm) {
    while (vm->grayCount > 0) {
        // Pop an item from the gray stack.
        Obj* obj = vm->gray[--vm->grayCount];
        blackenObject(vm, obj);
    }
}