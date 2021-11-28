#ifndef mochi_debug_h
#define mochi_debug_h

#include "vm.h"

// Prints a disassembly of the given chunk, using the given name as a header.
void disassembleChunk(MochiVM* chunk, const char* name);
// Prints a disassembly of the instruction at the offset within the given chunk.
// Returns the offset of the next instruction, since instructions may have
// differing size.
int disassembleInstruction(MochiVM* chunk, int offset);
// Prints the full value stack of the given fiber.
void printFiberValueStack(MochiVM* vm, ObjFiber* fiber);
// Prints the full frame stack of the given fiber.
void printFiberFrameStack(MochiVM* vm, ObjFiber* fiber);
// Prints the full root stack of the given fiber.
void printFiberRootStack(MochiVM* vm, ObjFiber* fiber);

static inline void debugTraceExecution(MochiVM* vm, ObjFiber* fiber) {
#if MOCHIVM_DEBUG_TRACE_EXECUTION
    disassembleInstruction(vm, (int)(fiber->ip - vm->code.data));
#endif
}

static inline void debugTraceValueStack(MochiVM* vm, ObjFiber* fiber) {
#if MOCHIVM_DEBUG_TRACE_VALUE_STACK
    printFiberValueStack(vm, fiber);
#endif
}

static inline void debugTraceFrameStack(MochiVM* vm, ObjFiber* fiber) {
#if MOCHIVM_DEBUG_TRACE_FRAME_STACK
    printFiberFrameStack(vm, fiber);
#endif
}

static inline void debugTraceRootStack(MochiVM* vm, ObjFiber* fiber) {
#if MOCHIVM_DEBUG_TRACE_ROOT_STACK
    printFiberRootStack(vm, fiber);
#endif
}

#endif