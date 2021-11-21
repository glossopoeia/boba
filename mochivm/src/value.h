#ifndef mochivm_value_h
#define mochivm_value_h

#include <string.h>

#include "common.h"
#include "mochivm.h"

extern const TableKey TABLE_KEY_UNUSED;
extern const TableKey TABLE_KEY_TOMBSTONE;
extern const TableKey TABLE_KEY_RANGE_START;

typedef enum
{
    VAL_BOOL,
    VAL_I8,
    VAL_U8,
    VAL_I16,
    VAL_U16,
    VAL_I32,
    VAL_U32,
    VAL_I64,
    VAL_U64,
    VAL_SINGLE,
    VAL_DOUBLE
} ValueType;

typedef enum
{
    OBJ_I64,
    OBJ_U64,
    OBJ_DOUBLE,
    OBJ_LIST,
    OBJ_FIBER,
    OBJ_VAR_FRAME,
    OBJ_CALL_FRAME,
    OBJ_HANDLE_FRAME,
    OBJ_CLOSURE,
    OBJ_CONTINUATION,
    OBJ_FOREIGN,
    OBJ_C_POINTER,
    OBJ_FOREIGN_RESUME,
    OBJ_ARRAY,
    OBJ_SLICE,
    OBJ_BYTE_ARRAY,
    OBJ_BYTE_SLICE,
    OBJ_REF,
    OBJ_STRUCT,
    OBJ_RECORD,
    OBJ_VARIANT
} ObjType;

// Base struct for all heap-allocated object types.
struct Obj {
    ObjType type;
    // Used during garbage collection
    bool isMarked;

    // All currently allocated objects are maintained in a linked list.
    // This allows all memory to be reachable during garbage collection.
    struct Obj* next;
};

// Some internal representations don't support full 64-bit
// value types, so we have heap allocated versions.

typedef struct ObjI64 {
    Obj obj;
    int64_t val;
} ObjI64;

typedef struct ObjU64 {
    Obj obj;
    uint64_t val;
} ObjU64;

typedef struct ObjDouble {
    Obj obj;
    double val;
} ObjDouble;

#if MOCHIVM_POINTER_TAGGING

#include "value_ptr_tagged.h"

#elif MOCHIVM_NAN_TAGGING

#include "value_nan_tagged.h"

#else

#include "value_union.h"

#endif

DECLARE_BUFFER(Byte, uint8_t);
DECLARE_BUFFER(Int, int);
DECLARE_BUFFER(Value, Value);

typedef struct {
    // The entry's key. 0 if not in use & available, 1 if tombstone, >1 for actual value.
    // A tombstone is an entry that was previously in use but is now deleted.
    TableKey key;

    // Allows a table to support 'scoped' keys, having multiple values for the same key and
    // only being able to get the most-recently inserted value for that key.
    int nesting;

    // The value associated with the key.
    Value value;
} TableEntry;

// A hash table mapping keys to values.
//
// We use something very simple: open addressing with linear probing. The hash
// table is an array of entries. Each entry is a key-value pair. If the key is
// either 0 or 1, it indicates no value is currently in that slot.
// Otherwise, it's a valid key, and the value is the value associated with it.
//
// When entries are added, the array is dynamically scaled by GROW_FACTOR to
// keep the number of filled slots under MAP_LOAD_PERCENT. Likewise, if the map
// gets empty enough, it will be resized to a smaller array. When this happens,
// all existing entries are rehashed and re-added to the new array.
//
// When an entry is removed, its slot is replaced with a "tombstone". This is an
// entry whose key is 1. When probing
// for a key, we will continue past tombstones, because the desired key may be
// found after them if the key that was removed was part of a prior collision.
// When the array gets resized, all tombstones are discarded.
typedef struct {
    // The number of entries allocated.
    uint32_t capacity;

    // The number of entries in the map.
    uint32_t count;

    // Pointer to a contiguous array of [capacity] entries.
    TableEntry* entries;
} Table;

static inline void valueArrayCopy(Value* dest, Value* src, int count) {
    memcpy(dest, src, sizeof(Value) * count);
}

ObjI64* mochiNewI64(MochiVM* vm, int64_t val);
ObjU64* mochiNewU64(MochiVM* vm, uint64_t val);
ObjDouble* mochiNewDouble(MochiVM* vm, double val);

// Creates a new empty table.
Table* mochiNewTable(MochiVM* vm);
void mochiTableInit(Table* table);
// Create a clone of an existing table.
Table* mochiTableClone(MochiVM* vm, Table* existing, bool scoped);
// Looks up [key] in [table]. If found, returns true and sets the out Value from the entry.
// Otherwise, sets `FALSE_VAL` as the out Value and returns false.
bool mochiTableGet(Table* table, TableKey key, Value* out);
// Associates [key] with [value] in [table].
void mochiTableSet(MochiVM* vm, Table* table, TableKey key, Value value);
void mochiTableSetScoped(MochiVM* vm, Table* table, TableKey key, Value value);
void mochiTableClear(MochiVM* vm, Table* table);
// Removes [key] from [table], if present. Returns true if found or false otherwise.
bool mochiTableTryRemove(MochiVM* vm, Table* table, TableKey key);
bool mochiTableTryRemoveScoped(MochiVM* vm, Table* table, TableKey key);

// Logs a textual representation of the given value to the output
void printValue(MochiVM* vm, Value value);

#endif