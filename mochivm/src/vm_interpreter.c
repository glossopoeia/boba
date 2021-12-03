#include <stdio.h>
#include <string.h>

#include "common.h"
#include "debug.h"
#include "memory.h"
#include "vm.h"

#if MOCHIVM_BATTERY_UV
#include "battery_uv.h"
#include "uv.h"
#endif

#if MOCHIVM_BATTERY_SDL
#include "battery_sdl.h"
#endif

// Generic function to create a call frame from a closure based on some data
// known about it. Can supply a var frame that will be spliced between the
// parameters and the captured values, but if this isn't needed, supply NULL
// for it. Modifies the fiber stack, and expects the parameters to be in
// correct order at the top of the stack.
static ObjCallFrame* callClosureFrame(MochiVM* vm, ObjFiber* fiber, ObjClosure* capture, ObjVarFrame* frameVars,
                                      ObjContinuation* cont, uint8_t* after) {
    ASSERT(mochiFiberValueCount(fiber) >= capture->paramCount,
           "Not enough values on the value stack to call the closure.");

    int varCount = (cont != NULL ? 1 : 0) + capture->paramCount + capture->capturedCount +
                   (frameVars != NULL ? frameVars->slotCount : 0);
    Value* vars = ALLOCATE_ARRAY(vm, Value, varCount);

    int offset = 0;
    if (cont != NULL) {
        vars[0] = OBJ_VAL(cont);
        offset += 1;
    }

    for (int i = 0; i < capture->paramCount; i++) {
        vars[offset + i] = *(--fiber->valueStackTop);
    }
    offset += capture->paramCount;

    if (frameVars != NULL) {
        valueArrayCopy(vars + offset, frameVars->slots, frameVars->slotCount);
        offset += frameVars->slotCount;
    }
    valueArrayCopy(vars + offset, capture->captured, capture->capturedCount);
    return newCallFrame(vars, varCount, after, vm);
}

// Walk the frame stack backwards looking for a handle frame with the given
// handle id that is 'unnested', i.e. with a nesting level of 0. Injecting
// increases the nesting levels of the nearest handle frames with a given
// handle id, while ejecting decreases the nesting level. This dual
// functionality allows some actions to be handled by handlers 'containing'
// inner handlers that would otherwise have handled the action. This function
// drives the actual effect of the nesting by continuing to walk down handle
// frames even if a handle frame with the requested id is found if it is
// 'nested', i.e. with a nesting level greater than 0.
static int findFreeHandler(ObjFiber* fiber, int handleId) {
    int stackCount = fiber->frameStackTop - fiber->frameStack;
    int index = 0;
    for (; index < stackCount; index++) {
        ObjVarFrame* frame = *(fiber->frameStackTop - index - 1);
        if (frame->obj.type != OBJ_HANDLE_FRAME) {
            continue;
        }
        ObjHandleFrame* handle = (ObjHandleFrame*)frame;
        if (handle->handleId == handleId && handle->nesting == 0) {
            break;
        }
    }
    ASSERT(index < stackCount, "Could not find an unnested handle frame with the desired identifier.");
    return index;
}

static void restoreSaved(MochiVM* vm, ObjFiber* fiber, ObjHandleFrame* handle, ObjContinuation* cont, uint8_t* after) {
    // we basically copy it, but update the arguments passed along through the
    // handling context and forget the 'return location'
    ObjHandleFrame* updated =
        mochinewHandleFrame(vm, handle->handleId, handle->call.vars.slotCount, handle->handlerCount, after);
    updated->afterClosure = handle->afterClosure;
    OBJ_ARRAY_COPY(updated->handlers, handle->handlers, handle->handlerCount);
    // take any handle parameters off the stack
    for (int i = 0; i < handle->call.vars.slotCount; i++) {
        updated->call.vars.slots[i] = *(--fiber->valueStackTop);
    }

    // captured stack values go under any remaining stack values
    int remainingValues = fiber->valueStackTop - fiber->valueStack;
    valueArrayCopy(fiber->valueStack + cont->savedStackCount, fiber->valueStack, remainingValues);
    valueArrayCopy(fiber->valueStack, cont->savedStack, cont->savedStackCount);
    fiber->valueStackTop = fiber->valueStackTop + cont->savedStackCount;

    // saved frames just go on top of the existing frames
    *fiber->frameStackTop++ = (ObjVarFrame*)updated;
    OBJ_ARRAY_COPY(fiber->frameStackTop, cont->savedFrames + 1, cont->savedFramesCount - 1);
    fiber->frameStackTop = fiber->frameStackTop + (cont->savedFramesCount - 1);
}

// Dispatcher function to run a particular fiber in the context of the given
// vm.
static int run(MochiVM* vm, register ObjFiber* fiber) {
    register uint8_t* codeStart = vm->code.data;

#define FROM_START(offset) (codeStart + (int)(offset))

#define PUSH_VAL(value)  (*fiber->valueStackTop++ = value)
#define POP_VAL()        (*(--fiber->valueStackTop))
#define DROP_VALS(count) (fiber->valueStackTop = fiber->valueStackTop - (count))
#define PEEK_VAL(index)  (*(fiber->valueStackTop - (index)))
#define VALUE_COUNT()    (fiber->valueStackTop - fiber->valueStack)

#define PUSH_FRAME(frame)  (*fiber->frameStackTop++ = (ObjVarFrame*)(frame))
#define POP_FRAME()        (*(--fiber->frameStackTop))
#define DROP_FRAMES(count) (fiber->frameStackTop = fiber->frameStackTop - (count))
#define PEEK_FRAME(index)  (*(fiber->frameStackTop - (index)))
#define FRAME_COUNT()      (fiber->frameStackTop - fiber->frameStack)
#define FIND_VAL(frame, slot)  ((*(fiber->frameStackTop - 1 - (frame)))->slots[(slot)])

#define READ_BYTE()   (*fiber->ip++)
#define READ_SHORT()  (fiber->ip += 2, (int16_t)((fiber->ip[-2] << 8) | fiber->ip[-1]))
#define READ_USHORT() (fiber->ip += 2, (uint16_t)((fiber->ip[-2] << 8) | fiber->ip[-1]))
#define READ_INT()                                                                                                     \
    (fiber->ip += 4, (int32_t)((fiber->ip[-4] << 24) | (fiber->ip[-3] << 16) | (fiber->ip[-2] << 8) | fiber->ip[-1]))
#define READ_UINT()                                                                                                    \
    (fiber->ip += 4, (uint32_t)((fiber->ip[-4] << 24) | (fiber->ip[-3] << 16) | (fiber->ip[-2] << 8) | fiber->ip[-1]))
#define READ_CONSTANT() (vm->constants.data[READ_USHORT()])
#define UNARY_OP(paramType, paramExtract, retConstruct, op)                                                            \
    do {                                                                                                               \
        paramType n = paramExtract(POP_VAL());                                                                         \
        PUSH_VAL(retConstruct(vm, op n));                                                                              \
    } while (false)
#define BINARY_OP(paramType, paramExtract, retConstruct, op)                                                           \
    do {                                                                                                               \
        paramType a = paramExtract(POP_VAL());                                                                         \
        paramType b = paramExtract(POP_VAL());                                                                         \
        PUSH_VAL(retConstruct(vm, a op b));                                                                            \
    } while (false)
#define SIGN_OP(paramType, paramExtract)                                                                               \
    do {                                                                                                               \
        paramType a = paramExtract(POP_VAL());                                                                         \
        PUSH_VAL(I8_VAL(vm, (a > 0) - (a < 0)));                                                                       \
    } while (false)
// Integer division has several interesting flavors, some of which we
// implement. For a more in depth overview of these flavors, see
// https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/divmodnote-letter.pdf
#define DIV_REM_T(paramType, paramExtract, retConstruct)                                                               \
    do {                                                                                                               \
        paramType a = paramExtract(POP_VAL());                                                                         \
        paramType b = paramExtract(POP_VAL());                                                                         \
        PUSH_VAL(retConstruct(vm, a / b));                                                                             \
        PUSH_VAL(retConstruct(vm, a % b));                                                                             \
    } while (false)
#define DIV_REM_F(paramType, paramExtract, retConstruct)                                                               \
    do {                                                                                                               \
        paramType a = paramExtract(POP_VAL());                                                                         \
        paramType b = paramExtract(POP_VAL());                                                                         \
        paramType q = a / b;                                                                                           \
        paramType r = a % b;                                                                                           \
        if ((r > 0 && b < 0) || (r < 0 && b > 0)) {                                                                    \
            q = q - 1;                                                                                                 \
            r = r + b;                                                                                                 \
        }                                                                                                              \
        PUSH_VAL(retConstruct(vm, q));                                                                                 \
        PUSH_VAL(retConstruct(vm, r));                                                                                 \
    } while (false)
#define DIV_REM_E(paramType, paramExtract, retConstruct)                                                               \
    do {                                                                                                               \
        paramType a = paramExtract(POP_VAL());                                                                         \
        paramType b = paramExtract(POP_VAL());                                                                         \
        paramType q = a / b;                                                                                           \
        paramType r = a % b;                                                                                           \
        if (r < 0) {                                                                                                   \
            if (b > 0) {                                                                                               \
                q = q - 1;                                                                                             \
                r = r + b;                                                                                             \
            } else {                                                                                                   \
                q = q + 1;                                                                                             \
                r = r - b;                                                                                             \
            }                                                                                                          \
        }                                                                                                              \
    } while (false)

#if MOCHIVM_BATTERY_UV
#define UV_EVENT_LOOP()                                                                                                \
    do {                                                                                                               \
        uv_run(uv_default_loop(), UV_RUN_NOWAIT);                                                                      \
    } while (false);
#else
#define UV_EVENT_LOOP()                                                                                                \
    do {                                                                                                               \
    } while (false)
#endif

#define WAIT_GC()                                                                                                      \
    while (vm->collecting) {                                                                                           \
        fiber->isPausedForGc = true;                                                                                   \
    }                                                                                                                  \
    fiber->isPausedForGc = false

#if MOCHIVM_COMPUTED_GOTO

    static void* dispatchTable[] = {
#define OPCODE(name) &&code_##name,
#include "opcodes.h"
#undef OPCODE
    };

#define INTERPRET_LOOP  DISPATCH();
#define CASE_CODE(name) code_##name

#define DISPATCH()                                                                                                     \
    do {                                                                                                               \
        WAIT_GC();                                                                                                     \
        UV_EVENT_LOOP();                                                                                               \
        if (fiber->isSuspended) {                                                                                      \
            goto CASE_CODE(NOP);                                                                                       \
        }                                                                                                              \
        debugTraceValueStack(vm, fiber);                                                                               \
        debugTraceFrameStack(vm, fiber);                                                                               \
        debugTraceRootStack(vm, fiber);                                                                                \
        debugTraceExecution(vm, fiber);                                                                                \
        goto* dispatchTable[instruction = (Code)READ_BYTE()];                                                          \
    } while (false)

#else

#define INTERPRET_LOOP                                                                                                 \
    loop:                                                                                                              \
    WAIT_GC();                                                                                                         \
    UV_EVENT_LOOP();                                                                                                   \
    if (fiber->isSuspended) {                                                                                          \
        goto loop;                                                                                                     \
    }                                                                                                                  \
    debugTraceValueStack(vm, fiber);                                                                                   \
    debugTraceFrameStack(vm, fiber);                                                                                   \
    debugTraceRootStack(vm, fiber);                                                                                    \
    debugTraceExecution(vm, fiber);                                                                                    \
    switch (instruction = (Code)READ_BYTE())

#define CASE_CODE(name) case CODE_##name
#define DISPATCH()      goto loop

#endif

    Code instruction = CODE_NOP;
    INTERPRET_LOOP {
        CASE_CODE(NOP) : {
            DISPATCH();
        }
        CASE_CODE(BREAKPOINT) : {
            // TODO: implement debugger support, probably involving fiber suspension
            // and fiber resume function accessible as an external api
            ASSERT(false, "BREAKPOINT support is not yet implemented.");
            DISPATCH();
        }
        CASE_CODE(ABORT) : {
            uint8_t retCode = READ_BYTE();
            return retCode;
        }
        CASE_CODE(CONSTANT) : {
            Value constant = READ_CONSTANT();
            PUSH_VAL(constant);
            DISPATCH();
        }

        CASE_CODE(PERM_QUERY) : {
            int permId = READ_USHORT();
            PUSH_VAL(BOOL_VAL(vm, mochiHasPermission(vm, permId)));
            DISPATCH();
        }
        CASE_CODE(PERM_REQUEST) : {
            int permId = READ_USHORT();
            // TODO: this instruction probably needs to be integrated with
            // async/callbacks
            PUSH_VAL(BOOL_VAL(vm, mochiRequestPermission(vm, permId)));
            DISPATCH();
        }
        CASE_CODE(PERM_REQUEST_ALL) : {
            int permId = READ_USHORT();
            // TODO: this instruction probably needs to be integrated with
            // async/callbacks
            PUSH_VAL(BOOL_VAL(vm, mochiRequestAllPermissions(vm, permId)));
            DISPATCH();
        }
        CASE_CODE(PERM_REVOKE) : {
            int permId = READ_USHORT();
            mochiRevokePermission(vm, permId);
            DISPATCH();
        }
        CASE_CODE(JUMP_PERMISSION) : {
            int permId = READ_USHORT();
            uint8_t* newLoc = FROM_START(READ_UINT());
            if (mochiHasPermission(vm, permId)) {
                fiber->ip = newLoc;
            }
            DISPATCH();
        }
        CASE_CODE(OFFSET_PERMISSION) : {
            int permId = READ_USHORT();
            int offset = READ_INT();
            if (mochiHasPermission(vm, permId)) {
                fiber->ip += offset;
            }
            DISPATCH();
        }

        CASE_CODE(TRUE) : {
            PUSH_VAL(TRUE_VAL);
            DISPATCH();
        }
        CASE_CODE(FALSE) : {
            PUSH_VAL(FALSE_VAL);
            DISPATCH();
        }
        CASE_CODE(BOOL_NOT) : {
            bool b = AS_BOOL(POP_VAL());
            PUSH_VAL(BOOL_VAL(vm, !b));
            DISPATCH();
        }
        CASE_CODE(BOOL_AND) : {
            bool a = AS_BOOL(POP_VAL());
            bool b = AS_BOOL(POP_VAL());
            PUSH_VAL(BOOL_VAL(vm, a && b));
            DISPATCH();
        }
        CASE_CODE(BOOL_OR) : {
            bool a = AS_BOOL(POP_VAL());
            bool b = AS_BOOL(POP_VAL());
            PUSH_VAL(BOOL_VAL(vm, a || b));
            DISPATCH();
        }
        CASE_CODE(BOOL_NEQ) : {
            bool a = AS_BOOL(POP_VAL());
            bool b = AS_BOOL(POP_VAL());
            PUSH_VAL(BOOL_VAL(vm, a != b));
            DISPATCH();
        }
        CASE_CODE(BOOL_EQ) : {
            bool a = AS_BOOL(POP_VAL());
            bool b = AS_BOOL(POP_VAL());
            PUSH_VAL(BOOL_VAL(vm, a == b));
            DISPATCH();
        }

        CASE_CODE(I8) : {
            int8_t val;
            memcpy(&val, fiber->ip, 1);
            PUSH_VAL(I8_VAL(vm, val));
            fiber->ip += 1;
            DISPATCH();
        }
        CASE_CODE(U8) : {
            uint8_t val = READ_BYTE();
            PUSH_VAL(U8_VAL(vm, val));
            DISPATCH();
        }
        CASE_CODE(I16) : {
            int16_t val = READ_SHORT();
            PUSH_VAL(I16_VAL(vm, val));
            DISPATCH();
        }
        CASE_CODE(U16) : {
            uint16_t val = READ_USHORT();
            PUSH_VAL(U16_VAL(vm, val));
            DISPATCH();
        }
        CASE_CODE(I32) : {
            int32_t val = READ_INT();
            PUSH_VAL(I32_VAL(vm, val));
            DISPATCH();
        }
        CASE_CODE(U32) : {
            uint32_t val = READ_UINT();
            PUSH_VAL(U32_VAL(vm, val));
            DISPATCH();
        }
        CASE_CODE(I64) : {
            int64_t val =
                ((int64_t)fiber->ip[0] << 52) |
                ((int64_t)fiber->ip[1] << 48) |
                ((int64_t)fiber->ip[2] << 40) |
                ((int64_t)fiber->ip[3] << 32) |
                ((int64_t)fiber->ip[4] << 24) |
                ((int64_t)fiber->ip[5] << 16) |
                ((int64_t)fiber->ip[6] << 8) |
                (int64_t)fiber->ip[7];
            PUSH_VAL(I64_VAL(vm, val));
            fiber->ip += 8;
            DISPATCH();
        }
        CASE_CODE(U64) : {
            uint64_t val =
                ((uint64_t)fiber->ip[0] << 52) |
                ((uint64_t)fiber->ip[1] << 48) |
                ((uint64_t)fiber->ip[2] << 40) |
                ((uint64_t)fiber->ip[3] << 32) |
                ((uint64_t)fiber->ip[4] << 24) |
                ((uint64_t)fiber->ip[5] << 16) |
                ((uint64_t)fiber->ip[6] << 8) |
                (uint64_t)fiber->ip[7];
            PUSH_VAL(U64_VAL(vm, val));
            fiber->ip += 8;
            DISPATCH();
        }
        CASE_CODE(SINGLE) : {
            int32_t reint = READ_INT();
            float val;
            memcpy(&val, &reint, 4);
            PUSH_VAL(SINGLE_VAL(vm, val));
            DISPATCH();
        }
        CASE_CODE(DOUBLE) : {
            int64_t reint =
                ((int64_t)fiber->ip[0] << 52) |
                ((int64_t)fiber->ip[1] << 48) |
                ((int64_t)fiber->ip[2] << 40) |
                ((int64_t)fiber->ip[3] << 32) |
                ((int64_t)fiber->ip[4] << 24) |
                ((int64_t)fiber->ip[5] << 16) |
                ((int64_t)fiber->ip[6] << 8) |
                (int64_t)fiber->ip[7];
            double val;
            memcpy(&val, &reint, 8);
            PUSH_VAL(DOUBLE_VAL(vm, val));
            DISPATCH();
        }
        CASE_CODE(INT_NEG) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                UNARY_OP(int8_t, AS_I8, I8_VAL, -);
                DISPATCH();
            }
            case VAL_U8: {
                UNARY_OP(uint8_t, AS_U8, U8_VAL, -);
                DISPATCH();
            }
            case VAL_I16: {
                UNARY_OP(int16_t, AS_I16, I16_VAL, -);
                DISPATCH();
            }
            case VAL_U16: {
                UNARY_OP(uint16_t, AS_U16, U16_VAL, -);
                DISPATCH();
            }
            case VAL_I32: {
                UNARY_OP(int32_t, AS_I32, I32_VAL, -);
                DISPATCH();
            }
            case VAL_U32: {
                UNARY_OP(uint32_t, AS_U32, U32_VAL, -);
                DISPATCH();
            }
            case VAL_I64: {
                UNARY_OP(int64_t, AS_I64, I64_VAL, -);
                DISPATCH();
            }
            case VAL_U64: {
                UNARY_OP(uint64_t, AS_U64, U64_VAL, -);
                DISPATCH();
            }
            }
        }
        CASE_CODE(INT_INC) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                UNARY_OP(int8_t, AS_I8, I8_VAL, ++);
                DISPATCH();
            }
            case VAL_U8: {
                UNARY_OP(uint8_t, AS_U8, U8_VAL, ++);
                DISPATCH();
            }
            case VAL_I16: {
                UNARY_OP(int16_t, AS_I16, I16_VAL, ++);
                DISPATCH();
            }
            case VAL_U16: {
                UNARY_OP(uint16_t, AS_U16, U16_VAL, ++);
                DISPATCH();
            }
            case VAL_I32: {
                UNARY_OP(int32_t, AS_I32, I32_VAL, ++);
                DISPATCH();
            }
            case VAL_U32: {
                UNARY_OP(uint32_t, AS_U32, U32_VAL, ++);
                DISPATCH();
            }
            case VAL_I64: {
                UNARY_OP(int64_t, AS_I64, I64_VAL, ++);
                DISPATCH();
            }
            case VAL_U64: {
                UNARY_OP(uint64_t, AS_U64, U64_VAL, ++);
                DISPATCH();
            }
            }
        }
        CASE_CODE(INT_DEC) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                UNARY_OP(int8_t, AS_I8, I8_VAL, --);
                DISPATCH();
            }
            case VAL_U8: {
                UNARY_OP(uint8_t, AS_U8, U8_VAL, --);
                DISPATCH();
            }
            case VAL_I16: {
                UNARY_OP(int16_t, AS_I16, I16_VAL, --);
                DISPATCH();
            }
            case VAL_U16: {
                UNARY_OP(uint16_t, AS_U16, U16_VAL, --);
                DISPATCH();
            }
            case VAL_I32: {
                UNARY_OP(int32_t, AS_I32, I32_VAL, --);
                DISPATCH();
            }
            case VAL_U32: {
                UNARY_OP(uint32_t, AS_U32, U32_VAL, --);
                DISPATCH();
            }
            case VAL_I64: {
                UNARY_OP(int64_t, AS_I64, I64_VAL, --);
                DISPATCH();
            }
            case VAL_U64: {
                UNARY_OP(uint64_t, AS_U64, U64_VAL, --);
                DISPATCH();
            }
            }
        }
        CASE_CODE(INT_ADD) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                BINARY_OP(int8_t, AS_I8, I8_VAL, +);
                DISPATCH();
            }
            case VAL_U8: {
                BINARY_OP(uint8_t, AS_U8, U8_VAL, +);
                DISPATCH();
            }
            case VAL_I16: {
                BINARY_OP(int16_t, AS_I16, I16_VAL, +);
                DISPATCH();
            }
            case VAL_U16: {
                BINARY_OP(uint16_t, AS_U16, U16_VAL, +);
                DISPATCH();
            }
            case VAL_I32: {
                BINARY_OP(int32_t, AS_I32, I32_VAL, +);
                DISPATCH();
            }
            case VAL_U32: {
                BINARY_OP(uint32_t, AS_U32, U32_VAL, +);
                DISPATCH();
            }
            case VAL_I64: {
                BINARY_OP(int64_t, AS_I64, I64_VAL, +);
                DISPATCH();
            }
            case VAL_U64: {
                BINARY_OP(uint64_t, AS_U64, U64_VAL, +);
                DISPATCH();
            }
            }
        }
        CASE_CODE(INT_SUB) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                BINARY_OP(int8_t, AS_I8, I8_VAL, -);
                DISPATCH();
            }
            case VAL_U8: {
                BINARY_OP(uint8_t, AS_U8, U8_VAL, -);
                DISPATCH();
            }
            case VAL_I16: {
                BINARY_OP(int16_t, AS_I16, I16_VAL, -);
                DISPATCH();
            }
            case VAL_U16: {
                BINARY_OP(uint16_t, AS_U16, U16_VAL, -);
                DISPATCH();
            }
            case VAL_I32: {
                BINARY_OP(int32_t, AS_I32, I32_VAL, -);
                DISPATCH();
            }
            case VAL_U32: {
                BINARY_OP(uint32_t, AS_U32, U32_VAL, -);
                DISPATCH();
            }
            case VAL_I64: {
                BINARY_OP(int64_t, AS_I64, I64_VAL, -);
                DISPATCH();
            }
            case VAL_U64: {
                BINARY_OP(uint64_t, AS_U64, U64_VAL, -);
                DISPATCH();
            }
            }
        }
        CASE_CODE(INT_MUL) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                BINARY_OP(int8_t, AS_I8, I8_VAL, *);
                DISPATCH();
            }
            case VAL_U8: {
                BINARY_OP(uint8_t, AS_U8, U8_VAL, *);
                DISPATCH();
            }
            case VAL_I16: {
                BINARY_OP(int16_t, AS_I16, I16_VAL, *);
                DISPATCH();
            }
            case VAL_U16: {
                BINARY_OP(uint16_t, AS_U16, U16_VAL, *);
                DISPATCH();
            }
            case VAL_I32: {
                BINARY_OP(int32_t, AS_I32, I32_VAL, *);
                DISPATCH();
            }
            case VAL_U32: {
                BINARY_OP(uint32_t, AS_U32, U32_VAL, *);
                DISPATCH();
            }
            case VAL_I64: {
                BINARY_OP(int64_t, AS_I64, I64_VAL, *);
                DISPATCH();
            }
            case VAL_U64: {
                BINARY_OP(uint64_t, AS_U64, U64_VAL, *);
                DISPATCH();
            }
            }
        }
        CASE_CODE(INT_DIV_REM_T) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                DIV_REM_T(int8_t, AS_I8, I8_VAL);
                DISPATCH();
            }
            case VAL_U8: {
                DIV_REM_T(uint8_t, AS_U8, U8_VAL);
                DISPATCH();
            }
            case VAL_I16: {
                DIV_REM_T(int16_t, AS_I16, I16_VAL);
                DISPATCH();
            }
            case VAL_U16: {
                DIV_REM_T(uint16_t, AS_U16, U16_VAL);
                DISPATCH();
            }
            case VAL_I32: {
                DIV_REM_T(int32_t, AS_I32, I32_VAL);
                DISPATCH();
            }
            case VAL_U32: {
                DIV_REM_T(uint32_t, AS_U32, U32_VAL);
                DISPATCH();
            }
            case VAL_I64: {
                DIV_REM_T(int64_t, AS_I64, I64_VAL);
                DISPATCH();
            }
            case VAL_U64: {
                DIV_REM_T(uint64_t, AS_U64, U64_VAL);
                DISPATCH();
            }
            }
        }
        CASE_CODE(INT_DIV_REM_F) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                DIV_REM_F(int8_t, AS_I8, I8_VAL);
                DISPATCH();
            }
            case VAL_I16: {
                DIV_REM_F(int16_t, AS_I16, I16_VAL);
                DISPATCH();
            }
            case VAL_I32: {
                DIV_REM_F(int32_t, AS_I32, I32_VAL);
                DISPATCH();
            }
            case VAL_I64: {
                DIV_REM_F(int64_t, AS_I64, I64_VAL);
                DISPATCH();
            }
            }
        }
        CASE_CODE(INT_DIV_REM_E) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                DIV_REM_E(int8_t, AS_I8, I8_VAL);
                DISPATCH();
            }
            case VAL_I16: {
                DIV_REM_E(int16_t, AS_I16, I16_VAL);
                DISPATCH();
            }
            case VAL_I32: {
                DIV_REM_E(int32_t, AS_I32, I32_VAL);
                DISPATCH();
            }
            case VAL_I64: {
                DIV_REM_E(int64_t, AS_I64, I64_VAL);
                DISPATCH();
            }
            }
        }
        CASE_CODE(INT_OR) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                BINARY_OP(int8_t, AS_I8, I8_VAL, |);
                DISPATCH();
            }
            case VAL_U8: {
                BINARY_OP(uint8_t, AS_U8, U8_VAL, |);
                DISPATCH();
            }
            case VAL_I16: {
                BINARY_OP(int16_t, AS_I16, I16_VAL, |);
                DISPATCH();
            }
            case VAL_U16: {
                BINARY_OP(uint16_t, AS_U16, U16_VAL, |);
                DISPATCH();
            }
            case VAL_I32: {
                BINARY_OP(int32_t, AS_I32, I32_VAL, |);
                DISPATCH();
            }
            case VAL_U32: {
                BINARY_OP(uint32_t, AS_U32, U32_VAL, |);
                DISPATCH();
            }
            case VAL_I64: {
                BINARY_OP(int64_t, AS_I64, I64_VAL, |);
                DISPATCH();
            }
            case VAL_U64: {
                BINARY_OP(uint64_t, AS_U64, U64_VAL, |);
                DISPATCH();
            }
            }
        }
        CASE_CODE(INT_AND) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                BINARY_OP(int8_t, AS_I8, I8_VAL, &);
                DISPATCH();
            }
            case VAL_U8: {
                BINARY_OP(uint8_t, AS_U8, U8_VAL, &);
                DISPATCH();
            }
            case VAL_I16: {
                BINARY_OP(int16_t, AS_I16, I16_VAL, &);
                DISPATCH();
            }
            case VAL_U16: {
                BINARY_OP(uint16_t, AS_U16, U16_VAL, &);
                DISPATCH();
            }
            case VAL_I32: {
                BINARY_OP(int32_t, AS_I32, I32_VAL, &);
                DISPATCH();
            }
            case VAL_U32: {
                BINARY_OP(uint32_t, AS_U32, U32_VAL, &);
                DISPATCH();
            }
            case VAL_I64: {
                BINARY_OP(int64_t, AS_I64, I64_VAL, &);
                DISPATCH();
            }
            case VAL_U64: {
                BINARY_OP(uint64_t, AS_U64, U64_VAL, &);
                DISPATCH();
            }
            }
        }
        CASE_CODE(INT_XOR) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                BINARY_OP(int8_t, AS_I8, I8_VAL, ^);
                DISPATCH();
            }
            case VAL_U8: {
                BINARY_OP(uint8_t, AS_U8, U8_VAL, ^);
                DISPATCH();
            }
            case VAL_I16: {
                BINARY_OP(int16_t, AS_I16, I16_VAL, ^);
                DISPATCH();
            }
            case VAL_U16: {
                BINARY_OP(uint16_t, AS_U16, U16_VAL, ^);
                DISPATCH();
            }
            case VAL_I32: {
                BINARY_OP(int32_t, AS_I32, I32_VAL, ^);
                DISPATCH();
            }
            case VAL_U32: {
                BINARY_OP(uint32_t, AS_U32, U32_VAL, ^);
                DISPATCH();
            }
            case VAL_I64: {
                BINARY_OP(int64_t, AS_I64, I64_VAL, ^);
                DISPATCH();
            }
            case VAL_U64: {
                BINARY_OP(uint64_t, AS_U64, U64_VAL, ^);
                DISPATCH();
            }
            }
        }
        CASE_CODE(INT_COMP) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                UNARY_OP(int8_t, AS_I8, I8_VAL, ~);
                DISPATCH();
            }
            case VAL_U8: {
                UNARY_OP(uint8_t, AS_U8, U8_VAL, ~);
                DISPATCH();
            }
            case VAL_I16: {
                UNARY_OP(int16_t, AS_I16, I16_VAL, ~);
                DISPATCH();
            }
            case VAL_U16: {
                UNARY_OP(uint16_t, AS_U16, U16_VAL, ~);
                DISPATCH();
            }
            case VAL_I32: {
                UNARY_OP(int32_t, AS_I32, I32_VAL, ~);
                DISPATCH();
            }
            case VAL_U32: {
                UNARY_OP(uint32_t, AS_U32, U32_VAL, ~);
                DISPATCH();
            }
            case VAL_I64: {
                UNARY_OP(int64_t, AS_I64, I64_VAL, ~);
                DISPATCH();
            }
            case VAL_U64: {
                UNARY_OP(uint64_t, AS_U64, U64_VAL, ~);
                DISPATCH();
            }
            }
        }
        CASE_CODE(INT_SHL) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                BINARY_OP(int8_t, AS_I8, I8_VAL, <<);
                DISPATCH();
            }
            case VAL_U8: {
                BINARY_OP(uint8_t, AS_U8, U8_VAL, <<);
                DISPATCH();
            }
            case VAL_I16: {
                BINARY_OP(int16_t, AS_I16, I16_VAL, <<);
                DISPATCH();
            }
            case VAL_U16: {
                BINARY_OP(uint16_t, AS_U16, U16_VAL, <<);
                DISPATCH();
            }
            case VAL_I32: {
                BINARY_OP(int32_t, AS_I32, I32_VAL, <<);
                DISPATCH();
            }
            case VAL_U32: {
                BINARY_OP(uint32_t, AS_U32, U32_VAL, <<);
                DISPATCH();
            }
            case VAL_I64: {
                BINARY_OP(int64_t, AS_I64, I64_VAL, <<);
                DISPATCH();
            }
            case VAL_U64: {
                BINARY_OP(uint64_t, AS_U64, U64_VAL, <<);
                DISPATCH();
            }
            }
        }
        CASE_CODE(INT_SHR) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                BINARY_OP(int8_t, AS_I8, I8_VAL, >>);
                DISPATCH();
            }
            case VAL_U8: {
                BINARY_OP(uint8_t, AS_U8, U8_VAL, >>);
                DISPATCH();
            }
            case VAL_I16: {
                BINARY_OP(int16_t, AS_I16, I16_VAL, >>);
                DISPATCH();
            }
            case VAL_U16: {
                BINARY_OP(uint16_t, AS_U16, U16_VAL, >>);
                DISPATCH();
            }
            case VAL_I32: {
                BINARY_OP(int32_t, AS_I32, I32_VAL, >>);
                DISPATCH();
            }
            case VAL_U32: {
                BINARY_OP(uint32_t, AS_U32, U32_VAL, >>);
                DISPATCH();
            }
            case VAL_I64: {
                BINARY_OP(int64_t, AS_I64, I64_VAL, >>);
                DISPATCH();
            }
            case VAL_U64: {
                BINARY_OP(uint64_t, AS_U64, U64_VAL, >>);
                DISPATCH();
            }
            }
        }
        CASE_CODE(INT_EQ) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                BINARY_OP(int8_t, AS_I8, BOOL_VAL, ==);
                DISPATCH();
            }
            case VAL_U8: {
                BINARY_OP(uint8_t, AS_U8, BOOL_VAL, ==);
                DISPATCH();
            }
            case VAL_I16: {
                BINARY_OP(int16_t, AS_I16, BOOL_VAL, ==);
                DISPATCH();
            }
            case VAL_U16: {
                BINARY_OP(uint16_t, AS_U16, BOOL_VAL, ==);
                DISPATCH();
            }
            case VAL_I32: {
                BINARY_OP(int32_t, AS_I32, BOOL_VAL, ==);
                DISPATCH();
            }
            case VAL_U32: {
                BINARY_OP(uint32_t, AS_U32, BOOL_VAL, ==);
                DISPATCH();
            }
            case VAL_I64: {
                BINARY_OP(int64_t, AS_I64, BOOL_VAL, ==);
                DISPATCH();
            }
            case VAL_U64: {
                BINARY_OP(uint64_t, AS_U64, BOOL_VAL, ==);
                DISPATCH();
            }
            }
        }
        CASE_CODE(INT_LESS) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                BINARY_OP(int8_t, AS_I8, BOOL_VAL, <);
                DISPATCH();
            }
            case VAL_U8: {
                BINARY_OP(uint8_t, AS_U8, BOOL_VAL, <);
                DISPATCH();
            }
            case VAL_I16: {
                BINARY_OP(int16_t, AS_I16, BOOL_VAL, <);
                DISPATCH();
            }
            case VAL_U16: {
                BINARY_OP(uint16_t, AS_U16, BOOL_VAL, <);
                DISPATCH();
            }
            case VAL_I32: {
                BINARY_OP(int32_t, AS_I32, BOOL_VAL, <);
                DISPATCH();
            }
            case VAL_U32: {
                BINARY_OP(uint32_t, AS_U32, BOOL_VAL, <);
                DISPATCH();
            }
            case VAL_I64: {
                BINARY_OP(int64_t, AS_I64, BOOL_VAL, <);
                DISPATCH();
            }
            case VAL_U64: {
                BINARY_OP(uint64_t, AS_U64, BOOL_VAL, <);
                DISPATCH();
            }
            }
        }
        CASE_CODE(INT_GREATER) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                BINARY_OP(int8_t, AS_I8, BOOL_VAL, >);
                DISPATCH();
            }
            case VAL_U8: {
                BINARY_OP(uint8_t, AS_U8, BOOL_VAL, >);
                DISPATCH();
            }
            case VAL_I16: {
                BINARY_OP(int16_t, AS_I16, BOOL_VAL, >);
                DISPATCH();
            }
            case VAL_U16: {
                BINARY_OP(uint16_t, AS_U16, BOOL_VAL, >);
                DISPATCH();
            }
            case VAL_I32: {
                BINARY_OP(int32_t, AS_I32, BOOL_VAL, >);
                DISPATCH();
            }
            case VAL_U32: {
                BINARY_OP(uint32_t, AS_U32, BOOL_VAL, >);
                DISPATCH();
            }
            case VAL_I64: {
                BINARY_OP(int64_t, AS_I64, BOOL_VAL, >);
                DISPATCH();
            }
            case VAL_U64: {
                BINARY_OP(uint64_t, AS_U64, BOOL_VAL, >);
                DISPATCH();
            }
            }
        }
        CASE_CODE(INT_SIGN) : {
            switch (READ_BYTE()) {
            case VAL_I8: {
                SIGN_OP(int8_t, AS_I8);
                DISPATCH();
            }
            case VAL_I16: {
                SIGN_OP(int16_t, AS_I16);
                DISPATCH();
            }
            case VAL_I32: {
                SIGN_OP(int32_t, AS_I32);
                DISPATCH();
            }
            case VAL_I64: {
                SIGN_OP(int64_t, AS_I64);
                DISPATCH();
            }
            }
        }

        CASE_CODE(SINGLE_NEG) : {
            UNARY_OP(float, AS_SINGLE, SINGLE_VAL, -);
            DISPATCH();
        }
        CASE_CODE(SINGLE_ADD) : {
            BINARY_OP(float, AS_SINGLE, SINGLE_VAL, +);
            DISPATCH();
        }
        CASE_CODE(SINGLE_SUB) : {
            BINARY_OP(float, AS_SINGLE, SINGLE_VAL, -);
            DISPATCH();
        }
        CASE_CODE(SINGLE_MUL) : {
            BINARY_OP(float, AS_SINGLE, SINGLE_VAL, *);
            DISPATCH();
        }
        CASE_CODE(SINGLE_DIV) : {
            BINARY_OP(float, AS_SINGLE, SINGLE_VAL, /);
            DISPATCH();
        }
        CASE_CODE(SINGLE_EQ) : {
            BINARY_OP(float, AS_SINGLE, BOOL_VAL, ==);
            DISPATCH();
        }
        CASE_CODE(SINGLE_LESS) : {
            BINARY_OP(float, AS_SINGLE, BOOL_VAL, <);
            DISPATCH();
        }
        CASE_CODE(SINGLE_GREATER) : {
            BINARY_OP(float, AS_SINGLE, BOOL_VAL, >);
            DISPATCH();
        }
        CASE_CODE(SINGLE_SIGN) : {
            SIGN_OP(float, AS_SINGLE);
            DISPATCH();
        }

        CASE_CODE(DOUBLE_NEG) : {
            UNARY_OP(double, AS_DOUBLE, DOUBLE_VAL, -);
            DISPATCH();
        }
        CASE_CODE(DOUBLE_ADD) : {
            BINARY_OP(double, AS_DOUBLE, DOUBLE_VAL, +);
            DISPATCH();
        }
        CASE_CODE(DOUBLE_SUB) : {
            BINARY_OP(double, AS_DOUBLE, DOUBLE_VAL, -);
            DISPATCH();
        }
        CASE_CODE(DOUBLE_MUL) : {
            BINARY_OP(double, AS_DOUBLE, DOUBLE_VAL, *);
            DISPATCH();
        }
        CASE_CODE(DOUBLE_DIV) : {
            BINARY_OP(double, AS_DOUBLE, DOUBLE_VAL, /);
            DISPATCH();
        }
        CASE_CODE(DOUBLE_EQ) : {
            BINARY_OP(double, AS_DOUBLE, BOOL_VAL, ==);
            DISPATCH();
        }
        CASE_CODE(DOUBLE_LESS) : {
            BINARY_OP(double, AS_DOUBLE, BOOL_VAL, <);
            DISPATCH();
        }
        CASE_CODE(DOUBLE_GREATER) : {
            BINARY_OP(double, AS_DOUBLE, BOOL_VAL, >);
            DISPATCH();
        }
        CASE_CODE(DOUBLE_SIGN) : {
            SIGN_OP(double, AS_DOUBLE);
            DISPATCH();
        }

#define CAST_FROM(fromC, fromMacro)                                                                                    \
    switch (to) {                                                                                                      \
    case VAL_BOOL: {                                                                                                   \
        UNARY_OP(fromC, fromMacro, BOOL_VAL, (bool));                                                                  \
        DISPATCH();                                                                                                    \
    }                                                                                                                  \
    case VAL_I8: {                                                                                                     \
        UNARY_OP(fromC, fromMacro, I8_VAL, (int8_t));                                                                  \
        DISPATCH();                                                                                                    \
    }                                                                                                                  \
    case VAL_U8: {                                                                                                     \
        UNARY_OP(fromC, fromMacro, U8_VAL, (uint8_t));                                                                 \
        DISPATCH();                                                                                                    \
    }                                                                                                                  \
    case VAL_I16: {                                                                                                    \
        UNARY_OP(fromC, fromMacro, I16_VAL, (int16_t));                                                                \
        DISPATCH();                                                                                                    \
    }                                                                                                                  \
    case VAL_U16: {                                                                                                    \
        UNARY_OP(fromC, fromMacro, U16_VAL, (uint16_t));                                                               \
        DISPATCH();                                                                                                    \
    }                                                                                                                  \
    case VAL_I32: {                                                                                                    \
        UNARY_OP(fromC, fromMacro, I32_VAL, (int32_t));                                                                \
        DISPATCH();                                                                                                    \
    }                                                                                                                  \
    case VAL_U32: {                                                                                                    \
        UNARY_OP(fromC, fromMacro, U32_VAL, (uint32_t));                                                               \
        DISPATCH();                                                                                                    \
    }                                                                                                                  \
    case VAL_I64: {                                                                                                    \
        UNARY_OP(fromC, fromMacro, I64_VAL, (int64_t));                                                                \
        DISPATCH();                                                                                                    \
    }                                                                                                                  \
    case VAL_U64: {                                                                                                    \
        UNARY_OP(fromC, fromMacro, U64_VAL, (uint64_t));                                                               \
        DISPATCH();                                                                                                    \
    }                                                                                                                  \
    case VAL_SINGLE: {                                                                                                 \
        UNARY_OP(fromC, fromMacro, SINGLE_VAL, (float));                                                               \
        DISPATCH();                                                                                                    \
    }                                                                                                                  \
    case VAL_DOUBLE: {                                                                                                 \
        UNARY_OP(fromC, fromMacro, DOUBLE_VAL, (double));                                                              \
        DISPATCH();                                                                                                    \
    }                                                                                                                  \
    }

        CASE_CODE(VALUE_CONV) : {
            uint8_t from = READ_BYTE();
            uint8_t to = READ_BYTE();
            switch (from) {
            case VAL_BOOL: {
                CAST_FROM(bool, AS_BOOL)
                break;
            }
            case VAL_I8: {
                CAST_FROM(int8_t, AS_I8)
                break;
            }
            case VAL_U8: {
                CAST_FROM(uint8_t, AS_U8)
                break;
            }
            case VAL_I16: {
                CAST_FROM(int16_t, AS_I16)
                break;
            }
            case VAL_U16: {
                CAST_FROM(uint16_t, AS_U16)
                break;
            }
            case VAL_I32: {
                CAST_FROM(int32_t, AS_I32)
                break;
            }
            case VAL_U32: {
                CAST_FROM(uint32_t, AS_U32)
                break;
            }
            case VAL_I64: {
                CAST_FROM(int64_t, AS_I64)
                break;
            }
            case VAL_U64: {
                CAST_FROM(uint64_t, AS_U64)
                break;
            }
            case VAL_SINGLE: {
                CAST_FROM(float, AS_SINGLE)
                break;
            }
            case VAL_DOUBLE: {
                CAST_FROM(double, AS_DOUBLE)
                break;
            }
            }
        }

        CASE_CODE(STORE) : {
            uint8_t varCount = READ_BYTE();
            ASSERT(VALUE_COUNT() >= varCount, "Not enough values to store in frame in STORE");

            Value* vars = ALLOCATE_ARRAY(vm, Value, varCount);
            for (int i = 0; i < (int)varCount; i++) {
                vars[i] = PEEK_VAL(i + 1);
            }

            ObjVarFrame* frame = newVarFrame(vars, varCount, vm);
            PUSH_FRAME(frame);

            DROP_VALS(varCount);
            DISPATCH();
        }
        CASE_CODE(FIND) : {
            uint16_t frameIdx = READ_USHORT();
            uint16_t slotIdx = READ_USHORT();

            ASSERT(FRAME_COUNT() > frameIdx, "FIND tried to access a frame outside "
                                             "the bounds of the frame stack.");
            ObjVarFrame* frame = PEEK_FRAME(frameIdx + 1);
            ASSERT(frame->slotCount > slotIdx, "FIND tried to access a slot outside "
                                               "the bounds of the frames slots.");
            PUSH_VAL(frame->slots[slotIdx]);
            DISPATCH();
        }
        CASE_CODE(OVERWRITE) : {
            uint16_t frameIdx = READ_USHORT();
            uint16_t slotIdx = READ_USHORT();

            ASSERT(FRAME_COUNT() > frameIdx, "OVERWRITE tried to access a frame outside "
                                             "the bounds of the frame stack.");
            ObjVarFrame* frame = PEEK_FRAME(frameIdx + 1);
            ASSERT(frame->slotCount > slotIdx, "OVERWRITE tried to access a slot outside "
                                               "the bounds of the frames slots.");

            frame->slots[slotIdx] = POP_VAL();
            DISPATCH();
        }
        CASE_CODE(FORGET) : {
            ASSERT(FRAME_COUNT() > 0, "FORGET expects at least one frame on the frame stack.");
            DROP_FRAMES(1);
            DISPATCH();
        }

        CASE_CODE(CALL_FOREIGN) : {
            int16_t fnIndex = READ_SHORT();
            ASSERT(vm->foreignFns.count > fnIndex, "CALL_FOREIGN attempted to address a method outside the bounds of "
                                                   "the foreign function collection.");
            MochiVMForeignMethodFn fn = vm->foreignFns.data[fnIndex];
            fn(vm, fiber);
            DISPATCH();
        }
        CASE_CODE(CALL) : {
            uint8_t* callPtr = FROM_START(READ_UINT());
            ObjCallFrame* frame = newCallFrame(NULL, 0, fiber->ip, vm);
            PUSH_FRAME((ObjVarFrame*)frame);
            fiber->ip = callPtr;
            DISPATCH();
        }
        CASE_CODE(TAILCALL) : {
            fiber->ip = FROM_START(READ_UINT());
            DISPATCH();
        }
        CASE_CODE(CALL_CLOSURE) : {
            ASSERT(FRAME_COUNT() > 0, "CALL_CLOSURE requires at least one frame on the frame stack.");
            ASSERT(VALUE_COUNT() > 0, "CALL_CLOSURE requires at least one value on the value stack.");

            ObjClosure* closure = AS_CLOSURE(POP_VAL());
            uint8_t* next = closure->funcLocation;

            // need to populate the frame with the captured values, but also the
            // parameters from the stack top of the stack is first in the frame, next
            // is second, etc. captured are copied as they appear in the closure
            mochiFiberPushRoot(fiber, (Obj*)closure);
            ObjCallFrame* frame = callClosureFrame(vm, fiber, closure, NULL, NULL, fiber->ip);
            mochiFiberPopRoot(fiber);

            // jump to the closure body and push the frame
            fiber->ip = next;
            PUSH_FRAME(frame);
            DISPATCH();
        }
        CASE_CODE(TAILCALL_CLOSURE) : {
            ASSERT(FRAME_COUNT() > 0, "TAILCALL_CLOSURE requires at least one frame on the frame stack.");
            ASSERT(VALUE_COUNT() > 0, "TAILCALL_CLOSURE requires at least one value on the value stack.");

            ObjClosure* closure = AS_CLOSURE(POP_VAL());
            uint8_t* next = closure->funcLocation;

            // create a new frame with the new array of stored values but the same
            // return location as the previous frame
            ObjCallFrame* oldFrame = (ObjCallFrame*)PEEK_FRAME(1);
            mochiFiberPushRoot(fiber, (Obj*)closure);
            ObjCallFrame* frame = callClosureFrame(vm, fiber, closure, NULL, NULL, oldFrame->afterLocation);
            mochiFiberPopRoot(fiber);

            // jump to the closure body, drop the old frame and push the new frame
            fiber->ip = next;
            DROP_FRAMES(1);
            PUSH_FRAME(frame);
            DISPATCH();
        }
        CASE_CODE(OFFSET) : {
            int offset = READ_INT();
            fiber->ip = fiber->ip + offset;
            DISPATCH();
        }
        CASE_CODE(RETURN) : {
            ASSERT(FRAME_COUNT() > 0, "RETURN expects at least one frame on the stack.");
            ObjCallFrame* frame = (ObjCallFrame*)POP_FRAME();
            ASSERT_OBJ_TYPE(frame, OBJ_CALL_FRAME, "RETURN expects a frame of type 'call frame' on the frame stack.");
            fiber->ip = frame->afterLocation;
            DISPATCH();
        }

        CASE_CODE(JUMP_TRUE) : {
            ASSERT(VALUE_COUNT() > 0, "JUMP_TRUE expects at least one boolean on the value stack.");
            uint8_t* newLoc = FROM_START(READ_UINT());
            bool val = AS_BOOL(POP_VAL());
            if (val) {
                fiber->ip = newLoc;
            }
            DISPATCH();
        }
        CASE_CODE(JUMP_FALSE) : {
            ASSERT(VALUE_COUNT() > 0, "JUMP_FALSE expects at least one boolean on the value stack.");
            uint8_t* newLoc = FROM_START(READ_UINT());
            bool val = AS_BOOL(POP_VAL());
            if (!val) {
                fiber->ip = newLoc;
            }
            DISPATCH();
        }
        CASE_CODE(OFFSET_TRUE) : {
            ASSERT(VALUE_COUNT() > 0, "OFFSET_TRUE expects at least one boolean on the value stack.");
            int offset = READ_INT();
            bool val = AS_BOOL(POP_VAL());
            if (val) {
                fiber->ip += offset;
            }
            DISPATCH();
        }
        CASE_CODE(OFFSET_FALSE) : {
            ASSERT(VALUE_COUNT() > 0, "OFFSET_FALSE expects at least one boolean on the value stack.");
            int offset = READ_INT();
            bool val = AS_BOOL(POP_VAL());
            if (!val) {
                fiber->ip += offset;
            }
            DISPATCH();
        }

        CASE_CODE(CLOSURE) : {
            uint8_t* bodyLocation = FROM_START(READ_UINT());
            uint8_t paramCount = READ_BYTE();
            uint16_t closedCount = READ_USHORT();
            ASSERT(paramCount + closedCount <= MOCHIVM_MAX_CALL_FRAME_SLOTS,
                   "Attempt to create closure with more slots than available.");

            ObjClosure* closure = mochiNewClosure(vm, bodyLocation, paramCount, closedCount);
            for (int i = 0; i < closedCount; i++) {
                uint16_t frameIdx = READ_USHORT();
                uint16_t slotIdx = READ_USHORT();

                ASSERT(FRAME_COUNT() > frameIdx, "Frame index out of range during CLOSURE creation.");
#ifndef NDEBUG
                ObjVarFrame* frame = PEEK_FRAME(frameIdx + 1);
                ASSERT(frame->slotCount >= slotIdx, "Slot index out of range during CLOSURE creation.");
#endif

                mochiClosureCapture(closure, i, FIND_VAL(frameIdx, slotIdx));
            }
            PUSH_VAL(OBJ_VAL(closure));
            DISPATCH();
        }
        CASE_CODE(RECURSIVE) : {
            uint8_t* bodyLocation = FROM_START(READ_UINT());
            uint8_t paramCount = READ_BYTE();
            uint16_t closedCount = READ_USHORT();
            ASSERT(paramCount + closedCount + 1 <= MOCHIVM_MAX_CALL_FRAME_SLOTS,
                   "Attempt to create recursive closure with more slots than "
                   "available.");

            // add one to closed count to save a slot for the closure itself
            ObjClosure* closure = mochiNewClosure(vm, bodyLocation, paramCount, closedCount + 1);
            // capture everything listed in the instruction args, saving the first
            // spot for the closure itself
            mochiClosureCapture(closure, 0, OBJ_VAL(closure));
            for (int i = 0; i < closedCount; i++) {
                uint16_t frameIdx = READ_USHORT();
                uint16_t slotIdx = READ_USHORT();

                ASSERT(FRAME_COUNT() > frameIdx, "Frame index out of range during CLOSURE creation.");
#ifndef NDEBUG
                ObjVarFrame* frame = PEEK_FRAME(frameIdx + 1);
                ASSERT(frame->slotCount >= slotIdx, "Slot index out of range during CLOSURE creation.");
#endif

                mochiClosureCapture(closure, i + 1, FIND_VAL(frameIdx, slotIdx));
            }
            PUSH_VAL(OBJ_VAL(closure));
            DISPATCH();
        }
        CASE_CODE(MUTUAL) : {
            uint8_t mutualCount = READ_BYTE();
            ASSERT(VALUE_COUNT() >= mutualCount, "MUTUAL closures attempted to be created with fewer than "
                                                 "requested on the value stack.");

            // for each soon-to-be mutually referenced closure,
            // make a new closure with room for references to
            // the other closures and itself
            for (int i = 0; i < mutualCount; i++) {
                ObjClosure* old = AS_CLOSURE(PEEK_VAL(mutualCount - i));
                ObjClosure* closure =
                    mochiNewClosure(vm, old->funcLocation, old->paramCount, old->capturedCount + mutualCount);
                valueArrayCopy(closure->captured + mutualCount, old->captured, old->capturedCount);
                // replace the old closure with the new one
                PEEK_VAL(mutualCount - i) = OBJ_VAL((Obj*)closure);
            }

            // finally, make the closures all reference each other in the same order
            for (int i = 0; i < mutualCount; i++) {
                ObjClosure* closure = AS_CLOSURE(PEEK_VAL(mutualCount - i));
                valueArrayCopy(fiber->valueStackTop - mutualCount, closure->captured, mutualCount);
            }

            DISPATCH();
        }
        CASE_CODE(CLOSURE_ONCE) : {
            ASSERT(VALUE_COUNT() > 0, "CLOSURE_ONCE expects at least one closure on the value stack.");
            ObjClosure* closure = AS_CLOSURE(PEEK_VAL(1));
            closure->resumeLimit = RESUME_ONCE;
            DISPATCH();
        }
        CASE_CODE(CLOSURE_ONCE_TAIL) : {
            ASSERT(VALUE_COUNT() > 0, "CLOSURE_ONCE_TAIL expects at least one "
                                      "closure on the value stack.");
            ObjClosure* closure = AS_CLOSURE(PEEK_VAL(1));
            closure->resumeLimit = RESUME_ONCE_TAIL;
            DISPATCH();
        }
        CASE_CODE(CLOSURE_MANY) : {
            ASSERT(VALUE_COUNT() > 0, "CLOSURE_MANY expects at least one closure on the value stack.");
            ObjClosure* closure = AS_CLOSURE(PEEK_VAL(1));
            closure->resumeLimit = RESUME_MANY;
            DISPATCH();
        }

        CASE_CODE(HANDLE) : {
            int16_t afterOffset = READ_SHORT();
            int handleId = (int)READ_UINT();
            uint8_t paramCount = READ_BYTE();
            uint8_t handlerCount = READ_BYTE();

            // plus one for the implicit 'after' closure that will be called by
            // COMPLETE
            ASSERT(VALUE_COUNT() >= handlerCount + paramCount + 1,
                   "HANDLE did not have the required number of values on the stack.");

            ObjHandleFrame* frame =
                mochinewHandleFrame(vm, handleId, paramCount, handlerCount, fiber->ip + afterOffset);
            // take the handlers off the stack
            for (int i = 0; i < handlerCount; i++) {
                frame->handlers[i] = AS_CLOSURE(POP_VAL());
            }
            frame->afterClosure = AS_CLOSURE(POP_VAL());
            // take any handle parameters off the stack
            for (int i = 0; i < paramCount; i++) {
                frame->call.vars.slots[i] = POP_VAL();
            }

            PUSH_FRAME(frame);
            DISPATCH();
        }
        CASE_CODE(INJECT) : {
            int handleId = READ_UINT();

            for (int i = 0; i < fiber->frameStackTop - fiber->frameStack; i++) {
                ObjVarFrame* frame = *(fiber->frameStackTop - i - 1);
                if (frame->obj.type != OBJ_HANDLE_FRAME) {
                    continue;
                }
                ObjHandleFrame* handle = (ObjHandleFrame*)frame;
                if (handle->handleId == handleId) {
                    handle->nesting += 1;
                    if (handle->nesting == 1) {
                        break;
                    }
                }
            }

            DISPATCH();
        }
        CASE_CODE(EJECT) : {
            int handleId = READ_UINT();

            for (int i = 0; i < fiber->frameStackTop - fiber->frameStack; i++) {
                ObjVarFrame* frame = *(fiber->frameStackTop - i - 1);
                if (frame->obj.type != OBJ_HANDLE_FRAME) {
                    continue;
                }
                ObjHandleFrame* handle = (ObjHandleFrame*)frame;
                if (handle->handleId == handleId) {
                    handle->nesting -= 1;
                    if (handle->nesting <= 0) {
                        ASSERT(handle->nesting == 0, "EJECT instruction occurred without prior INJECT.");
                        break;
                    }
                }
            }

            DISPATCH();
        }
        CASE_CODE(COMPLETE) : {
            ASSERT(FRAME_COUNT() > 0, "COMPLETE expects at least one handle frame on the frame stack.");

            ObjHandleFrame* frame = (ObjHandleFrame*)PEEK_FRAME(1);

            ObjCallFrame* newFrame =
                callClosureFrame(vm, fiber, frame->afterClosure, (ObjVarFrame*)frame, NULL, frame->call.afterLocation);

            DROP_FRAMES(1);
            PUSH_FRAME(newFrame);
            fiber->ip = frame->afterClosure->funcLocation;
            DISPATCH();
        }
        CASE_CODE(ESCAPE) : {
            ASSERT(FRAME_COUNT() > 0, "ESCAPE expects at least one handle frame on the frame stack.");

            int handleId = READ_UINT();
            uint8_t handlerIdx = READ_BYTE();
            int frameIdx = findFreeHandler(fiber, handleId);
            int frameCount = frameIdx + 1;
            ObjHandleFrame* frame = (ObjHandleFrame*)PEEK_FRAME(frameIdx + 1);

            ASSERT(handlerIdx < frame->handlerCount, "ESCAPE: Requested handler index outside the bounds of the handle "
                                                     "frame handler set.");
            ObjClosure* handler = frame->handlers[handlerIdx];

            if (handler->resumeLimit == RESUME_NONE) {
                ObjCallFrame* newFrame =
                    callClosureFrame(vm, fiber, handler, (ObjVarFrame*)frame, NULL, frame->call.afterLocation);

                fiber->valueStackTop = fiber->valueStack;
                // drop all frames up to and including the found handle frame
                DROP_FRAMES(frameCount);
                PUSH_FRAME(newFrame);
            } else if (handler->resumeLimit == RESUME_ONCE_TAIL && frame->call.vars.slotCount == 0) {
                // TODO: does the condition for a handle context with no variables
                // actually matter?
                ObjCallFrame* newFrame = callClosureFrame(vm, fiber, handler, NULL, NULL, fiber->ip);
                PUSH_FRAME(newFrame);
            } else {
                ObjContinuation* cont = mochiNewContinuation(vm, fiber->ip, frame->call.vars.slotCount,
                                                             VALUE_COUNT() - handler->paramCount, frameCount);
                // save all frames up to and including the found handle frame
                OBJ_ARRAY_COPY(cont->savedFrames, fiber->frameStackTop - frameCount, frameCount);
                valueArrayCopy(cont->savedStack, fiber->valueStack, cont->savedStackCount);

                mochiFiberPushRoot(fiber, (Obj*)cont);
                ObjCallFrame* newFrame =
                    callClosureFrame(vm, fiber, handler, (ObjVarFrame*)frame, cont, frame->call.afterLocation);
                mochiFiberPopRoot(fiber);

                fiber->valueStackTop = fiber->valueStack;
                // drop all frames up to and including the found handle frame
                DROP_FRAMES(frameCount);
                PUSH_FRAME(newFrame);
            }

            fiber->ip = handler->funcLocation;

            DISPATCH();
        }
        CASE_CODE(CALL_CONTINUATION) : {
            ASSERT(VALUE_COUNT() > 0, "CALL_CONTINUATION expects at least one continuation value at the "
                                      "top of the value stack.");
            ObjContinuation* cont = AS_CONTINUATION(POP_VAL());
            mochiFiberPushRoot(fiber, (Obj*)cont);

            // the last frame in the saved frame stack is always the handle frame
            // action reacted on
            ObjHandleFrame* handle = (ObjHandleFrame*)cont->savedFrames[0];
            ASSERT_OBJ_TYPE(handle, OBJ_HANDLE_FRAME,
                            "CALL_CONTINUATION expected a handle frame at the bottom "
                            "of the continuation frame stack.");
            ASSERT(VALUE_COUNT() >= handle->call.vars.slotCount,
                   "CALL_CONTINUATION expected more values on the value stack than "
                   "were available for parameters.");

            restoreSaved(vm, fiber, handle, cont, fiber->ip);
            fiber->ip = cont->resumeLocation;

            mochiFiberPopRoot(fiber);
            DISPATCH();
        }
        CASE_CODE(TAILCALL_CONTINUATION) : {
            ASSERT(VALUE_COUNT() > 0, "TAILCALL_CONTINUATION expects at least one continuation value at "
                                      "the top of the value stack.");
            ASSERT(FRAME_COUNT() > 0, "TAILCALL_CONTINUATION expects at least one "
                                      "call frame at the top of the frame stack.");
            ObjContinuation* cont = AS_CONTINUATION(POP_VAL());
            mochiFiberPushRoot(fiber, (Obj*)cont);

            uint8_t* after = ((ObjCallFrame*)POP_FRAME())->afterLocation;

            // the last frame in the saved frame stack is always the handle frame
            // action reacted on
            ObjHandleFrame* handle = (ObjHandleFrame*)cont->savedFrames[0];
            ASSERT_OBJ_TYPE(handle, OBJ_HANDLE_FRAME,
                            "TAILCALL_CONTINUATION expected a handle frame at the "
                            "bottom of the continuation frame stack.");
            ASSERT(VALUE_COUNT() >= handle->call.vars.slotCount,
                   "TAILCALL_CONTINUATION expected more values on the value stack "
                   "than were available for parameters.");

            restoreSaved(vm, fiber, handle, cont, after);
            fiber->ip = cont->resumeLocation;

            mochiFiberPopRoot(fiber);
            DISPATCH();
        }

        CASE_CODE(THREAD_SPAWN) : {
            uint32_t threadIp = READ_UINT();
            mochiSpawnCall(vm, fiber, threadIp);
            DISPATCH();
        }
        CASE_CODE(THREAD_SPAWN_WITH) : {
            uint32_t threadIp = READ_UINT();
            uint32_t consumed = READ_UINT();
            mochiSpawnCallWith(vm, fiber, threadIp, consumed);
            DISPATCH();
        }
        CASE_CODE(THREAD_SPAWN_COPY) : {
            mochiSpawnCopy(vm, fiber);
            DISPATCH();
        }
        CASE_CODE(THREAD_CURRENT) : {
            PUSH_VAL(OBJ_VAL(fiber));
            DISPATCH();
        }
        CASE_CODE(THREAD_SLEEP) : {
            uint32_t millis = AS_U32(POP_VAL());
            time_t secs = millis / 1000;
            long int nanos = (millis % 1000) * 1000000;
            int32_t res = thrd_sleep(&(struct timespec){.tv_sec = secs, .tv_nsec = nanos}, NULL);
            PUSH_VAL(I32_VAL(vm, res));
            DISPATCH();
        }
        CASE_CODE(THREAD_YIELD) : {
            thrd_yield();
            DISPATCH();
        }
        CASE_CODE(THREAD_JOIN) : {
            ObjFiber* toJoin = AS_FIBER(PEEK_VAL(1));
            int threadRes = 0;
            int32_t res = thrd_join(toJoin->thread, &threadRes);
            DROP_VALS(1);
            PUSH_VAL(I32_VAL(vm, threadRes));
            PUSH_VAL(I32_VAL(vm, res));
            DISPATCH();
        }
        CASE_CODE(THREAD_EQUAL) : {
            ObjFiber* left = AS_FIBER(PEEK_VAL(1));
            ObjFiber* right = AS_FIBER(PEEK_VAL(2));
            bool eq = mochiFiberEqual(left, right);
            DROP_VALS(2);
            PUSH_VAL(BOOL_VAL(vm, eq));
            DISPATCH();
        }

        CASE_CODE(ZAP) : {
            ASSERT(VALUE_COUNT() >= 1, "ZAP expects at least one value on the value stack.");
            DROP_VALS(1);
            DISPATCH();
        }
        CASE_CODE(DUP) : {
            ASSERT(VALUE_COUNT() >= 1, "DUP expects at least one value on the value stack.");
            Value top = PEEK_VAL(1);
            PUSH_VAL(top);
            DISPATCH();
        }
        CASE_CODE(SWAP) : {
            ASSERT(VALUE_COUNT() >= 2, "SWAP expects at least two values on the value stack.");
            Value top = POP_VAL();
            Value below = POP_VAL();
            PUSH_VAL(top);
            PUSH_VAL(below);
            DISPATCH();
        }
        CASE_CODE(SHUFFLE) : {
            uint8_t pop = READ_BYTE();
            uint8_t push = READ_BYTE();
            ASSERT(VALUE_COUNT() >= pop, "SHUFFLE expected more values on the stack than were available.");

            for (int i = 0; i < push; i++) {
                uint8_t index = READ_BYTE();
                Value val = PEEK_VAL(index + 1);
                PUSH_VAL(val);
            }

            valueArrayCopy(fiber->valueStackTop - push - pop, fiber->valueStackTop - push, push);
            fiber->valueStackTop -= pop;
            DISPATCH();
        }

        CASE_CODE(LIST_NIL) : {
            PUSH_VAL(OBJ_VAL(NULL));
            DISPATCH();
        }
        CASE_CODE(LIST_CONS) : {
            ASSERT(VALUE_COUNT() >= 2, "LIST_CONS expects at least two values on the value stack.");
            Value elem = PEEK_VAL(1);
            ObjList* tail = AS_LIST(PEEK_VAL(2));
            ObjList* new = mochiListCons(vm, elem, tail);
            DROP_VALS(2);
            PUSH_VAL(OBJ_VAL(new));
            DISPATCH();
        }
        CASE_CODE(LIST_HEAD) : {
            ASSERT(VALUE_COUNT() >= 1, "LIST_HEAD expects at least one value on the value stack.");
            ObjList* list = AS_LIST(POP_VAL());
            // TODO: if empty list, throw an exception here? assumes built-in or
            // standard library exception mechanism
            ASSERT(list != NULL, "LIST_HEAD cannot operate on an empty list.");
            ASSERT_OBJ_TYPE(list, OBJ_LIST, "LIST_HEAD can only operate on objects of list type.");
            PUSH_VAL(list->elem);
            DISPATCH();
        }
        CASE_CODE(LIST_TAIL) : {
            ASSERT(VALUE_COUNT() >= 1, "LIST_HEAD expects at least one value on the value stack.");
            ObjList* list = AS_LIST(POP_VAL());
            // TODO: if empty list, throw an exception here? assumes built-in or
            // standard library exception mechanism
            ASSERT(list != NULL, "LIST_HEAD cannot operate on an empty list.");
            ASSERT_OBJ_TYPE(list, OBJ_LIST, "LIST_HEAD can only operate on objects of list type.");
            PUSH_VAL(OBJ_VAL(list->next));
            DISPATCH();
        }
        CASE_CODE(LIST_IS_EMPTY) : {
            ASSERT(VALUE_COUNT() >= 1, "LIST_IS_EMPTY expects at least one value on the stack.");
            ObjList* list = AS_LIST(POP_VAL());
            PUSH_VAL(BOOL_VAL(vm, list == NULL));
            DISPATCH();
        }
        CASE_CODE(LIST_APPEND) : {
            ASSERT(VALUE_COUNT() >= 2, "LIST_APPEND expects at least two list values on the stack.");
            ObjList* prefix = AS_LIST(PEEK_VAL(1));
            ObjList* suffix = AS_LIST(PEEK_VAL(2));

            if (suffix == NULL) {
                DROP_VALS(2);
                PUSH_VAL(OBJ_VAL(prefix));
            } else if (prefix == NULL) {
                DROP_VALS(1);
            } else {
                ObjList* start = mochiListCons(vm, prefix->elem, NULL);
                ObjList* iter = start;
                prefix = prefix->next;

                mochiFiberPushRoot(fiber, (Obj*)start);
                while (prefix != NULL) {
                    iter->next = mochiListCons(vm, prefix->elem, NULL);
                    iter = iter->next;
                    prefix = prefix->next;
                }
                iter->next = suffix;
                mochiFiberPopRoot(fiber);

                DROP_VALS(2);
                PUSH_VAL(OBJ_VAL(start));
            }
            DISPATCH();
        }

        CASE_CODE(NEWREF) : {
            Value refInit = POP_VAL();
            // TODO: make this into a function: TableKey nextKey(vm)
            // TODO: make these two lines atomic/thread safe
            uint64_t key = vm->nextHeapKey;
            vm->nextHeapKey += 1;

            mochiTableSet(vm, &vm->heap, (TableKey)key, refInit);
            PUSH_VAL(OBJ_VAL(mochiNewRef(vm, key)));
            DISPATCH();
        }
        CASE_CODE(GETREF) : {
            ObjRef* ref = AS_REF(POP_VAL());
            Value val;
            mochiTableGet(&vm->heap, ref->ptr, &val);
            PUSH_VAL(val);
            DISPATCH();
        }
        CASE_CODE(PUTREF) : {
            Value val = PEEK_VAL(1);
            ObjRef* ref = AS_REF(PEEK_VAL(2));
            mochiTableSet(vm, &vm->heap, ref->ptr, val);
            DROP_VALS(2);
            DISPATCH();
        }

        CASE_CODE(CONSTRUCT) : {
            StructId structId = READ_UINT();
            uint8_t count = READ_BYTE();

            ObjStruct* stru = mochiNewStruct(vm, structId, count);
            // NOTE: this make the values in the struct ID conceptually 'backwards'
            // from how they were laid out on the stack, even though in memory its
            // the same order. The stack top pointer is at the end of the array, the
            // struct pointer is at the beginning. Doing it this way means we don't
            // have to reverse the elements, but might lead to conceptual confusion.
            // DOCUMENTATION REQUIRED
            valueArrayCopy(stru->elems, fiber->valueStackTop - count, count);
            DROP_VALS(count);
            PUSH_VAL(OBJ_VAL(stru));
            DISPATCH();
        }
        CASE_CODE(DESTRUCT) : {
            ObjStruct* stru = AS_STRUCT(POP_VAL());
            // NOTE: see note in CONSTRUCT instruction for a potential conceptual
            // pitfall.
            valueArrayCopy(fiber->valueStackTop, stru->elems, stru->count);
            fiber->valueStackTop += stru->count;
            DISPATCH();
        }
        CASE_CODE(IS_STRUCT) : {
            StructId structId = READ_UINT();
            ObjStruct* stru = AS_STRUCT(POP_VAL());
            PUSH_VAL(BOOL_VAL(vm, stru->id == structId));
            DISPATCH();
        }
        CASE_CODE(JUMP_STRUCT) : {
            StructId structId = READ_UINT();
            uint8_t* newLoc = FROM_START(READ_UINT());
            ObjStruct* stru = AS_STRUCT(POP_VAL());
            if (stru->id == structId) {
                fiber->ip = newLoc;
            }
            DISPATCH();
        }
        CASE_CODE(OFFSET_STRUCT) : {
            StructId structId = READ_UINT();
            int offset = READ_INT();
            ObjStruct* stru = AS_STRUCT(POP_VAL());
            if (stru->id == structId) {
                fiber->ip += offset;
            }
            DISPATCH();
        }

        CASE_CODE(RECORD_NIL) : {
            PUSH_VAL(OBJ_VAL(mochiNewRecord(vm)));
            DISPATCH();
        }
        CASE_CODE(RECORD_EXTEND) : {
            TableKey field = READ_UINT();
            ObjRecord* rec = mochiRecordExtend(vm, field, PEEK_VAL(1), AS_RECORD(PEEK_VAL(2)));
            DROP_VALS(2);
            PUSH_VAL(OBJ_VAL(rec));
            DISPATCH();
        }
        CASE_CODE(RECORD_SELECT) : {
            TableKey field = READ_UINT();
            Value v = mochiRecordSelect(field, AS_RECORD(POP_VAL()));
            PUSH_VAL(v);
            DISPATCH();
        }
        CASE_CODE(RECORD_RESTRICT) : {
            TableKey field = READ_UINT();
            ObjRecord* restr = mochiRecordRestrict(vm, field, AS_RECORD(PEEK_VAL(1)));
            PUSH_VAL(OBJ_VAL(restr));
            DROP_VALS(1);
            DISPATCH();
        }
        CASE_CODE(RECORD_UPDATE) : {
            TableKey field = READ_UINT();
            ObjRecord* rec = mochiRecordUpdate(vm, field, PEEK_VAL(1), AS_RECORD(PEEK_VAL(2)));
            DROP_VALS(2);
            PUSH_VAL(OBJ_VAL(rec));
            DISPATCH();
        }

        CASE_CODE(VARIANT) : {
            ObjVariant* var = mochiNewVariant(vm, READ_UINT(), POP_VAL());
            PUSH_VAL(OBJ_VAL(var));
            DISPATCH();
        }
        CASE_CODE(EMBED) : {
            TableKey label = READ_UINT();
            ObjVariant* var = mochiVariantEmbed(vm, label, AS_VARIANT(POP_VAL()));
            PUSH_VAL(OBJ_VAL(var));
            DISPATCH();
        }
        CASE_CODE(IS_CASE) : {
            TableKey label = READ_UINT();
            ObjVariant* var = AS_VARIANT(POP_VAL());
            PUSH_VAL(BOOL_VAL(vm, var->label == label));
            DISPATCH();
        }
        CASE_CODE(JUMP_CASE) : {
            TableKey label = READ_UINT();
            uint8_t* newLoc = FROM_START(READ_UINT());
            ObjVariant* var = AS_VARIANT(POP_VAL());
            if (var->label == label) {
                PUSH_VAL(var->elem);
                fiber->ip = newLoc;
            } else {
                PUSH_VAL(OBJ_VAL(var));
            }
            DISPATCH();
        }
        CASE_CODE(OFFSET_CASE) : {
            TableKey label = READ_UINT();
            int offset = READ_INT();
            ObjVariant* var = AS_VARIANT(POP_VAL());
            if (var->label == label) {
                PUSH_VAL(var->elem);
                fiber->ip += offset;
            } else {
                PUSH_VAL(OBJ_VAL(var));
            }
            DISPATCH();
        }

        CASE_CODE(ARRAY_NIL) : {
            PUSH_VAL(OBJ_VAL(mochiArrayNil(vm)));
            DISPATCH();
        }
        CASE_CODE(ARRAY_FILL) : {
            Value v = PEEK_VAL(1);
            int amt = (int)AS_U32(PEEK_VAL(2));
            ObjArray* arr = mochiArrayNil(vm);
            mochiFiberPushRoot(fiber, (Obj*)arr);
            arr = mochiArrayFill(vm, amt, v, arr);
            mochiFiberPopRoot(fiber);
            DROP_VALS(2);
            PUSH_VAL(OBJ_VAL(arr));
            DISPATCH();
        }
        CASE_CODE(ARRAY_SNOC) : {
            Value v = PEEK_VAL(1);
            ObjArray* arr = AS_ARRAY(PEEK_VAL(2));
            mochiArraySnoc(vm, v, arr);
            DROP_VALS(1);
            DISPATCH();
        }
        CASE_CODE(ARRAY_GET_AT) : {
            int idx = (int)AS_U32(POP_VAL());
            ObjArray* arr = AS_ARRAY(POP_VAL());
            PUSH_VAL(mochiArrayGetAt(idx, arr));
            DISPATCH();
        }
        CASE_CODE(ARRAY_SET_AT) : {
            int idx = (int)AS_U32(POP_VAL());
            Value val = PEEK_VAL(1);
            ObjArray* arr = AS_ARRAY(PEEK_VAL(2));
            mochiArraySetAt(idx, val, arr);
            DROP_VALS(1);
            DISPATCH();
        }
        CASE_CODE(ARRAY_LENGTH) : {
            ObjArray* arr = AS_ARRAY(POP_VAL());
            PUSH_VAL(U32_VAL(vm, mochiArrayLength(arr)));
            DISPATCH();
        }
        CASE_CODE(ARRAY_COPY) : {
            int start = (int)AS_U32(POP_VAL());
            int length = (int)AS_U32(POP_VAL());
            ObjArray* arr = AS_ARRAY(PEEK_VAL(1));
            PUSH_VAL(OBJ_VAL(mochiArrayCopy(vm, start, length, arr)));
            DISPATCH();
        }
        CASE_CODE(ARRAY_CONCAT) : {
            ObjArray* b = AS_ARRAY(PEEK_VAL(1));
            ObjArray* a = AS_ARRAY(PEEK_VAL(2));

            ObjArray* cat = mochiArrayNil(vm);
            for (int i = 0; i < a->elems.count; i++) {
                mochiArraySnoc(vm, a->elems.data[i], cat);
            }
            for (int i = 0; i < b->elems.count; i++) {
                mochiArraySnoc(vm, b->elems.data[i], cat);
            }
            DROP_VALS(2);
            PUSH_VAL(OBJ_VAL(cat));
            DISPATCH();
        }

        CASE_CODE(ARRAY_SLICE) : {
            int start = (int)AS_U32(POP_VAL());
            int length = (int)AS_U32(POP_VAL());
            ObjArray* arr = AS_ARRAY(PEEK_VAL(1));
            ObjSlice* slice = mochiArraySlice(vm, start, length, arr);
            DROP_VALS(1);
            PUSH_VAL(OBJ_VAL(slice));
            DISPATCH();
        }
        CASE_CODE(SUBSLICE) : {
            int start = (int)AS_U32(POP_VAL());
            int length = (int)AS_U32(POP_VAL());
            ObjSlice* orig = AS_SLICE(PEEK_VAL(1));
            ObjSlice* sub = mochiSubslice(vm, start, length, orig);
            DROP_VALS(1);
            PUSH_VAL(OBJ_VAL(sub));
            DISPATCH();
        }
        CASE_CODE(SLICE_GET_AT) : {
            int idx = (int)AS_U32(POP_VAL());
            ObjSlice* slice = AS_SLICE(POP_VAL());
            PUSH_VAL(mochiSliceGetAt(idx, slice));
            DISPATCH();
        }
        CASE_CODE(SLICE_SET_AT) : {
            int idx = (int)AS_U32(POP_VAL());
            Value val = PEEK_VAL(1);
            ObjSlice* slice = AS_SLICE(PEEK_VAL(2));
            mochiSliceSetAt(idx, val, slice);
            DROP_VALS(1);
            DISPATCH();
        }
        CASE_CODE(SLICE_LENGTH) : {
            ObjSlice* slice = AS_SLICE(POP_VAL());
            PUSH_VAL(U32_VAL(vm, mochiSliceLength(slice)));
            DISPATCH();
        }
        CASE_CODE(SLICE_COPY) : {
            ObjSlice* slice = AS_SLICE(PEEK_VAL(1));
            PUSH_VAL(OBJ_VAL(mochiSliceCopy(vm, slice)));
            DISPATCH();
        }

        CASE_CODE(BYTE_ARRAY_NIL) : {
            PUSH_VAL(OBJ_VAL(mochiByteArrayNil(vm)));
            DISPATCH();
        }
        CASE_CODE(BYTE_ARRAY_FILL) : {
            uint8_t v = AS_U8(POP_VAL());
            int amt = (int)AS_U32(POP_VAL());
            ObjByteArray* arr = mochiByteArrayNil(vm);
            mochiFiberPushRoot(fiber, (Obj*)arr);
            arr = mochiByteArrayFill(vm, amt, v, arr);
            mochiFiberPopRoot(fiber);
            PUSH_VAL(OBJ_VAL(arr));
            DISPATCH();
        }
        CASE_CODE(BYTE_ARRAY_SNOC) : {
            uint8_t v = AS_U8(POP_VAL());
            ObjByteArray* arr = AS_BYTE_ARRAY(PEEK_VAL(1));
            mochiByteArraySnoc(vm, v, arr);
            DISPATCH();
        }
        CASE_CODE(BYTE_ARRAY_GET_AT) : {
            int idx = (int)AS_U32(POP_VAL());
            ObjByteArray* arr = AS_BYTE_ARRAY(POP_VAL());
            PUSH_VAL(U8_VAL(vm, mochiByteArrayGetAt(idx, arr)));
            DISPATCH();
        }
        CASE_CODE(BYTE_ARRAY_SET_AT) : {
            int idx = (int)AS_U32(POP_VAL());
            uint8_t val = AS_U8(POP_VAL());
            ObjByteArray* arr = AS_BYTE_ARRAY(PEEK_VAL(1));
            mochiByteArraySetAt(idx, val, arr);
            DISPATCH();
        }
        CASE_CODE(BYTE_ARRAY_LENGTH) : {
            ObjByteArray* arr = AS_BYTE_ARRAY(POP_VAL());
            PUSH_VAL(U32_VAL(vm, mochiByteArrayLength(arr)));
            DISPATCH();
        }
        CASE_CODE(BYTE_ARRAY_COPY) : {
            int start = (int)AS_U32(POP_VAL());
            int length = (int)AS_U32(POP_VAL());
            ObjByteArray* arr = AS_BYTE_ARRAY(PEEK_VAL(1));
            PUSH_VAL(OBJ_VAL(mochiByteArrayCopy(vm, start, length, arr)));
            DISPATCH();
        }
        CASE_CODE(BYTE_ARRAY_CONCAT) : {
            ObjByteArray* b = AS_BYTE_ARRAY(PEEK_VAL(1));
            ObjByteArray* a = AS_BYTE_ARRAY(PEEK_VAL(2));

            ObjByteArray* cat = mochiByteArrayNil(vm);
            for (int i = 0; i < a->elems.count; i++) {
                mochiByteArraySnoc(vm, a->elems.data[i], cat);
            }
            for (int i = 0; i < b->elems.count; i++) {
                mochiByteArraySnoc(vm, b->elems.data[i], cat);
            }
            DROP_VALS(2);
            PUSH_VAL(OBJ_VAL(cat));
            DISPATCH();
        }

        CASE_CODE(BYTE_ARRAY_SLICE) : {
            int start = (int)AS_U32(POP_VAL());
            int length = (int)AS_U32(POP_VAL());
            ObjByteArray* arr = AS_BYTE_ARRAY(PEEK_VAL(1));
            ObjByteSlice* slice = mochiByteArraySlice(vm, start, length, arr);
            DROP_VALS(1);
            PUSH_VAL(OBJ_VAL(slice));
            DISPATCH();
        }
        CASE_CODE(BYTE_SUBSLICE) : {
            int start = (int)AS_U32(POP_VAL());
            int length = (int)AS_U32(POP_VAL());
            ObjByteSlice* orig = AS_BYTE_SLICE(PEEK_VAL(1));
            ObjByteSlice* sub = mochiByteSubslice(vm, start, length, orig);
            DROP_VALS(1);
            PUSH_VAL(OBJ_VAL(sub));
            DISPATCH();
        }
        CASE_CODE(BYTE_SLICE_GET_AT) : {
            int idx = (int)AS_U32(POP_VAL());
            ObjByteSlice* slice = AS_BYTE_SLICE(POP_VAL());
            PUSH_VAL(U8_VAL(vm, mochiByteSliceGetAt(idx, slice)));
            DISPATCH();
        }
        CASE_CODE(BYTE_SLICE_SET_AT) : {
            int idx = (int)AS_U32(POP_VAL());
            uint8_t val = AS_U8(POP_VAL());
            ObjByteSlice* slice = AS_BYTE_SLICE(PEEK_VAL(1));
            mochiByteSliceSetAt(idx, val, slice);
            DISPATCH();
        }
        CASE_CODE(BYTE_SLICE_LENGTH) : {
            ObjByteSlice* slice = AS_BYTE_SLICE(POP_VAL());
            PUSH_VAL(U32_VAL(vm, mochiByteSliceLength(slice)));
            DISPATCH();
        }
        CASE_CODE(BYTE_SLICE_COPY) : {
            ObjByteSlice* slice = AS_BYTE_SLICE(PEEK_VAL(1));
            PUSH_VAL(OBJ_VAL(mochiByteSliceCopy(vm, slice)));
            DISPATCH();
        }

        CASE_CODE(STRING_CONCAT) : {
            ObjByteArray* b = AS_BYTE_ARRAY(PEEK_VAL(1));
            ObjByteArray* a = AS_BYTE_ARRAY(PEEK_VAL(2));

            ObjByteArray* cat = mochiByteArrayNil(vm);
            mochiFiberPushRoot(fiber, (Obj*)cat);
            // count - 1 to remove the null-terminator character from the first string
            for (int i = 0; i < a->elems.count - 1; i++) {
                mochiByteArraySnoc(vm, a->elems.data[i], cat);
            }
            for (int i = 0; i < b->elems.count; i++) {
                mochiByteArraySnoc(vm, b->elems.data[i], cat);
            }
            mochiFiberPopRoot(fiber);
            DROP_VALS(2);
            PUSH_VAL(OBJ_VAL(cat));
            DISPATCH();
        }
        CASE_CODE(PRINT): {
            printf("%s", AS_CSTRING(PEEK_VAL(1)));
            DROP_VALS(1);
            DISPATCH();
        }
    }

    UNREACHABLE();
    return -1;

#undef READ_BYTE
#undef READ_SHORT
#undef READ_USHORT
#undef READ_INT
#undef READ_UINT
#undef READ_CONSTANT
}

int mochiInterpret(MochiVM* vm, ObjFiber* fiber) {
    return run(vm, fiber);
}

int mochiInterpretFirst(void* vmStart) {
    MochiVM* vm = vmStart;
    return run(vm, vm->fibers.data[0]);
}

int mochiRun(MochiVM* vm, int argc, const char* argv[]) {
#if MOCHIVM_DEBUG_DUMP_BYTECODE
    disassembleChunk(vm, "VM BYTECODE");
#endif

    mochiFiberBufferClear(vm, &vm->fibers);
    mochiFiberBufferWrite(vm, &vm->fibers, NULL);
    ObjFiber* fib = mochiNewFiber(vm, vm->code.data, NULL, 0);
    vm->fibers.data[0] = fib;

    /*ObjArray* args = mochiArrayNil(vm);
    mochiFiberPushValue(fib, OBJ_VAL(args));
    for (int i = 0; i < argc; i++) {
        ObjByteArray* arg = mochiByteArrayString(vm, argv[i]);
        mochiFiberPushRoot(fib, (Obj*)arg);
        mochiArraySnoc(vm, OBJ_VAL(arg), args);
        mochiFiberPopRoot(fib);
    }*/

    int threadStatus = thrd_create(&fib->thread, mochiInterpretFirst, vm);
    if (threadStatus != thrd_success) {
        printf("Couldn't create main thread.\n");
        return threadStatus;
    }

    // only wait for the main thread to finish
    int mainResult;
    int joinStatus = thrd_join(fib->thread, &mainResult);
    if (joinStatus != thrd_success) {
        printf("Couldn't join main thread with runner.\n");
        return joinStatus;
    }
#if MOCHIVM_BATTERY_UV
    uv_run(uv_default_loop(), UV_RUN_DEFAULT);
#endif
    return mainResult;
}