#include "battery_uv.h"
#include "debug.h"
#include "memory.h"
#include "uv.h"

// Generic function to create a call frame from a closure that will return to the fiber's 'current' location upon
// completion.
static ObjCallFrame* basicClosureFrame(MochiVM* vm, ObjFiber* fiber, ObjClosure* capture) {
    ASSERT(mochiFiberValueCount(fiber) >= capture->paramCount,
           "basicClosureFrame: Not enough values on the value stack to call the closure.");

    int varCount = capture->paramCount + capture->capturedCount;
    Value* vars = ALLOCATE_ARRAY(vm, Value, varCount);

    for (int i = 0; i < capture->paramCount; i++) {
        vars[i] = *(--fiber->valueStackTop);
    }
    int offset = capture->paramCount;

    valueArrayCopy(vars + offset, capture->captured, capture->capturedCount);
    return newCallFrame(vars, varCount, fiber->ip, vm);
}

void uvmochiNewTimer(MochiVM* vm, ObjFiber* fiber) {
    uv_timer_t* timer = vm->config.reallocateFn(NULL, sizeof(uv_timer_t), vm->config.userData);
    uv_timer_init(uv_default_loop(), timer);

    ObjCPointer* ptr = mochiNewCPointer(vm, timer);
    mochiFiberPushValue(fiber, OBJ_VAL(ptr));
}

void uvmochiCloseTimer(MochiVM* vm, ObjFiber* fiber) {
    ObjCPointer* ptr = (ObjCPointer*)AS_OBJ(mochiFiberPopValue(fiber));
    uv_timer_stop((uv_timer_t*)ptr->pointer);
    vm->config.reallocateFn(ptr->pointer, 0, vm->config.userData);
}

static void uvmochiTimerCallback(uv_timer_t* timer) {
    ForeignResume* res = (ForeignResume*)uv_req_get_data((uv_req_t*)timer);
    MochiVM* vm = res->vm;
    ObjFiber* fiber = res->fiber;

    ObjClosure* callback = AS_CLOSURE(mochiFiberPopValue(fiber));

    // get rid of the reference to the resume data
    mochiFiberPopRoot(fiber);

    // push the timer as the first argument to the callback
    Obj* obj = mochiFiberPopRoot(fiber);
    mochiFiberPushValue(fiber, OBJ_VAL(obj));

    // start the callback call
    mochiFiberPushRoot(fiber, (Obj*)callback);
    mochiFiberPushFrame(fiber, (ObjVarFrame*)basicClosureFrame(vm, fiber, callback));
    mochiFiberPopRoot(fiber);

    fiber->ip = callback->funcLocation;
    fiber->isSuspended = false;
}

void uvmochiTimerStart(MochiVM* vm, ObjFiber* fiber) {
    ASSERT(mochiFiberValueCount(fiber) >= 3, "Not enough values on the value stack to call uvmochiTimerStart.");

    fiber->isSuspended = true;

    ObjCPointer* ptr = (ObjCPointer*)AS_OBJ(mochiFiberPopValue(fiber));
    mochiFiberPushRoot(fiber, (Obj*)ptr);

    ForeignResume* res = mochiNewResume(vm, fiber);
    mochiFiberPushRoot(fiber, (Obj*)res);

    uint64_t duration = (uint64_t)AS_DOUBLE(mochiFiberPopValue(fiber));

    uv_req_set_data((uv_req_t*)ptr->pointer, res);
    uv_timer_start((uv_timer_t*)ptr->pointer, uvmochiTimerCallback, duration, 0);
}

void uvmochiTimerStop(MochiVM* vm, ObjFiber* fiber) {
    ASSERT(false, "uvmochiTimerStop not yet implemented.");
}

void uvmochiTimerSetRepeat(MochiVM* vm, ObjFiber* fiber) {
    ASSERT(false, "uvmochiTimerSetRepeat not yet implemented.");
}

void uvmochiTimerAgain(MochiVM* vm, ObjFiber* fiber) {
    ASSERT(false, "uvmochiTimerAgain not yet implemented.");
}