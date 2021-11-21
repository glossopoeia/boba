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

#endif