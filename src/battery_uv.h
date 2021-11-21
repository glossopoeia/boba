#ifndef mochivm_battery_uv_h
#define mochivm_battery_uv_h

#include "mochivm.h"

// Returns the libuv version packed into a single integer. 8 bits are used for each component, with the patch number
// stored in the 8 least significant bits. E.g. for libuv 1.2.3 this would be 0x010203.
//     a... --> a... I32
void uvmochiVersion(MochiVM* vm, ObjFiber* fiber);
// Returns the libuv version number as a string. For non-release versions the version suffix is included.
//     a... --> a... String
void uvmochiVersionString(MochiVM* vm, ObjFiber* fiber);

// Initializes a new timer object and pushes it to the stack.
//     a... --> a... V{ good: Timer, fail: String }
void uvmochiNewTimer(MochiVM* vm, ObjFiber* fiber);
// Properly releases the resources associated with the timer object on top of the stack, and pops it.
// WARNING: if multiple references to the timer exist, calling this function on those references will
// cause double-free problems. Accessing other references after one has been close is the same as
// accessing freed memory.
//     a... Timer --> a...
void uvmochiCloseTimer(MochiVM* vm, ObjFiber* fiber);
// Starts the timer on top of the stack with the given duration. The timer will execute the callback
// in the fourth stack slot when the duration has elapsed. Suspends the current fiber until the duration
// has elapsed. Places the timer reference on top of the stack for the callback.
//     a... (a... V{ good: Timer, fail: String } --> c...) U64 Timer ~~> c...
void uvmochiTimerStart(MochiVM* vm, ObjFiber* fiber);
void uvmochiTimerStop(MochiVM* vm, ObjFiber* fiber);
void uvmochiTimerSetRepeat(MochiVM* vm, ObjFiber* fiber);
void uvmochiTimerAgain(MochiVM* vm, ObjFiber* fiber);

// Opens a shared library. The filename is in utf-8. Returns 0 on success and -1 on error.
// Call uvmochiDlError to get the error message.
//     a... String --> a... V{ good: DynLib, fail: String }
void uvmochiDlOpen(MochiVM* vm, ObjFiber* fiber);
// Close the shared library.
//     a... DynLib --> a...
void uvmochiDlClose(MochiVM* vm, ObjFiber* fiber);
// Retrieves a data pointer from a dynamic library. It is legal for a symbol to map to NULL.
// Returns 0 on success and -1 if the symbol was not found.
//     a... DynLib String --> a... V{ good: DynSym, fail: String }
void uvmochiDlSym(MochiVM* vm, ObjFiber* fiber);

// Cross-platform implementation of gettimeofday(2).
//     a... --> a... V{ good: R{ sec: I64, usec: I32 }, fail: String }
void uvmochiGetTimeOfDay(MochiVM* vm, ObjFiber* fiber);
// Fill buf with exactly buflen cryptographically strong random bytes acquired from the system CSPRNG.
// flags is reserved for future extension and must currently be 0. Short reads are not possible. When
// less than buflen random bytes are available, a non-zero error value is returned or passed to the callback.
// The synchronous version may block indefinitely when not enough entropy is available. The asynchronous
// version may not ever finish when the system is low on entropy.
//     a... (a... V{ good: Array U8, fail: String } --> c...) (buflen: U32) (flags: U32) ~~> c...
void uvmochiRandom(MochiVM* vm, ObjFiber* fiber);
// Causes the calling thread to sleep for msec milliseconds.
//     a... U32 --> a...
void uvmochiSleep(MochiVM* vm, ObjFiber* fiber);

#endif