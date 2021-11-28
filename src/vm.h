#ifndef mochivm_vm_h
#define mochivm_vm_h

#include "object.h"
#include <threads.h>

typedef enum
{
#define OPCODE(name) CODE_##name,
#include "opcodes.h"
#undef OPCODE
} Code;

// The maximum number of temporary objects that can be made visible to the GC
// at one time.
#define MOCHIVM_MAX_TEMP_ROOTS 512

#define MOCHIVM_MAX_CALL_FRAME_SLOTS 65535
#define MOCHIVM_MAX_MARK_FRAME_SLOTS 256

DECLARE_BUFFER(ForeignFunction, MochiVMForeignMethodFn);
DECLARE_BUFFER(Fiber, ObjFiber*);

struct MochiVM {
    MochiVMConfiguration config;

    // Byte code and other buffers used for operation and disassembly.
    ByteBuffer code;
    IntBuffer lines;
    ValueBuffer constants;
    IntBuffer labelIndices;
    ValueBuffer labels;

    FiberBuffer fibers;

    // Shared mutable state among threads. Operations on the store are done using
    // reference values, which change the values stored in the table non-immutably.
    // TODO: rename this, it's more like a stateful value store, maybe just 'store'
    Table heap;
    TableKey nextHeapKey;

    // Memory management data:

    // Is the garbage collector currently running? Simple stop the world assumed.
    _Atomic(bool) collecting;
    // Provide a way to lock allocation so multiple threads don't start a GC pass simultaneously.
    mtx_t allocLock;

    // The number of bytes that are known to be currently allocated. Includes all
    // memory that was proven live after the last GC, as well as any new bytes
    // that were allocated since then. Does *not* include bytes for objects that
    // were freed since the last GC.
    size_t bytesAllocated;

    // The number of total allocated bytes that will trigger the next GC.
    size_t nextGC;

    // The first object in the linked list of all currently allocated objects.
    Obj* objects;

    // The "gray" set for the garbage collector. This is the stack of unprocessed
    // objects while a garbage collection pass is in process.
    Obj** gray;
    int grayCount;
    int grayCapacity;

    // The buffer of foreign function pointers the VM knows about.
    ForeignFunctionBuffer foreignFns;
};

bool mochiHasPermission(MochiVM* vm, int permissionId);
bool mochiRequestPermission(MochiVM* vm, int permissionId);
bool mochiRequestAllPermissions(MochiVM* vm, int permissionGroup);
void mochiRevokePermission(MochiVM* vm, int permissionId);

// Mark [obj] as reachable and still in use. This should only be called
// during the sweep phase of a garbage collection.
void mochiGrayObj(MochiVM* vm, Obj* obj);

// Mark [value] as reachable and still in use. This should only be called
// during the sweep phase of a garbage collection.
void mochiGrayValue(MochiVM* vm, Value value);

// Mark the values in [buffer] as reachable and still in use. This should only
// be called during the sweep phase of a garbage collection.
void mochiGrayBuffer(MochiVM* vm, ValueBuffer* buffer);

// Processes every object in the gray stack until all reachable objects have
// been marked. After that, all objects are either white (freeable) or black
// (in use and fully traversed).
void mochiBlackenObjects(MochiVM* vm);

#endif