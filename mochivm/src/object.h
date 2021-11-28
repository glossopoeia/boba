#ifndef mochivm_object_h
#define mochivm_object_h

#include "value.h"
#include <threads.h>

#define ASSERT_OBJ_TYPE(obj, objType, message) ASSERT(((Obj*)obj)->type == objType, message)
#define OBJ_ARRAY_COPY(objDest, objSrc, count) memcpy((Obj**)(objDest), (Obj**)(objSrc), sizeof(Obj*) * (count))

#define OBJ_TYPE(value) (AS_OBJ(value)->type)
#define OBJ_VAL(obj)    (mochiObjectToValue((Obj*)(obj)))

// These macros cast a Value to one of the specific object types. These do *not*
// perform any validation, so must only be used after the Value has been
// ensured to be the right type.
// AS_OBJ and AS_BOOL are implementation specific.
#define AS_VAR_FRAME(value)    ((ObjVarFrame*)AS_OBJ(value))
#define AS_CALL_FRAME(value)   ((ObjCallFrame*)AS_OBJ(value))
#define AS_HANDLE_FRAME(value) ((ObjHandleFrame*)AS_OBJ(value))
#define AS_CLOSURE(value)      ((ObjClosure*)AS_OBJ(value))
#define AS_CONTINUATION(value) ((ObjContinuation*)AS_OBJ(value))
#define AS_FIBER(v)            ((ObjFiber*)AS_OBJ(v))
#define AS_POINTER(v)          ((ObjCPointer*)AS_OBJ(v))
#define AS_FOREIGN(v)          ((ObjForeign*)AS_OBJ(v))
#define AS_LIST(v)             ((ObjList*)AS_OBJ(v))
#define AS_ARRAY(v)            ((ObjArray*)AS_OBJ(v))
#define AS_SLICE(v)            ((ObjSlice*)AS_OBJ(v))
#define AS_BYTE_ARRAY(v)       ((ObjByteArray*)AS_OBJ(v))
#define AS_BYTE_SLICE(v)       ((ObjByteSlice*)AS_OBJ(v))
#define AS_REF(v)              ((ObjRef*)AS_OBJ(v))
#define AS_STRUCT(v)           ((ObjStruct*)AS_OBJ(v))
#define AS_RECORD(v)           ((ObjRecord*)AS_OBJ(v))
#define AS_VARIANT(v)          ((ObjVariant*)AS_OBJ(v))
#define AS_CSTRING(v)          ((char*)(void*)((ObjByteArray*)AS_OBJ(v))->elems.data)

// This enum provides a way for compiler writers to specify that some closures-as-handlers have
// certain assumptions guaranteed that allow more efficient operation. For instance, RESUME_NONE
// will prevent a handler closure from capturing the continuation, since it is never resumed anyway,
// saving a potentially large allocation and copy. RESUME_ONCE_TAIL treats a handler closure call
// just like any other closure call. The most general option, but the least efficient, is RESUME_MANY,
// which can be thought of as the default for handler closures. The default for all closures is
// RESUME_MANY, even those which are never used as handlers, because continuation saving is only done
// during the ESCAPE instruction and so RESUME_MANY is never acted upon for the majority of closures.
typedef enum
{
    RESUME_NONE,
    RESUME_ONCE,
    RESUME_ONCE_TAIL,
    RESUME_MANY
} ResumeLimit;

// Represents a function combined with saved context. Arguments via [paramCount] are used to
// inject values from the stack into the call frame at the call site, rather than at
// closure creation time. [captured] stores the values captured from the frame stack at
// closure creation time. [paramCount] is highly useful for passing state through when using
// closures as action handlers, but also makes for a convenient shortcut to store function
// parameters in the frame stack. [resumeLimit] is a way for the runtime to specify how many times
// a closure-as-handler can resume in a handle context.
typedef struct ObjClosure {
    Obj obj;
    uint8_t* funcLocation;
    uint8_t paramCount;
    uint16_t capturedCount;
    ResumeLimit resumeLimit;
    Value captured[];
} ObjClosure;

typedef struct ObjVarFrame {
    Obj obj;
    Value* slots;
    int slotCount;
} ObjVarFrame;

typedef struct ObjCallFrame {
    ObjVarFrame vars;
    uint8_t* afterLocation;
} ObjCallFrame;

typedef struct ObjHandleFrame {
    ObjCallFrame call;
    // The identifier that will be searched for when trying to execute a particular operation. Designed to
    // enable efficiently finding sets of related handlers that all get handled by the same handler expression.
    // Trying to execute an operation must specify the 'set' of handlers the operation belongs to (handleId), then
    // the index within the set of the operation itself (handlers[i]).
    int handleId;
    int nesting;
    ObjClosure* afterClosure;
    ObjClosure** handlers;
    uint8_t handlerCount;
} ObjHandleFrame;

struct ObjFiber {
    Obj obj;
    uint8_t* ip;
    bool isSuspended;

    thrd_t thread;
    _Atomic(bool) isPausedForGc;

    // Value stack, upon which all instructions that consume and produce data operate.
    Value* valueStack;
    Value* valueStackTop;

    // Frame stack, upon which variable, function, and continuation instructions operate.
    ObjVarFrame** frameStack;
    ObjVarFrame** frameStackTop;

    // Root stack, a smaller Object stack used to temporarily store data so it doesn't get GC'ed.
    Obj** rootStack;
    Obj** rootStackTop;

    struct ObjFiber* caller;
};

typedef struct ObjContinuation {
    Obj obj;
    uint8_t* resumeLocation;
    uint8_t paramCount;
    Value* savedStack;
    int savedStackCount;
    ObjVarFrame** savedFrames;
    int savedFramesCount;
} ObjContinuation;

typedef struct ObjCPointer {
    Obj obj;
    void* pointer;
} ObjCPointer;

typedef struct ObjForeign {
    Obj obj;
    int dataCount;
    uint8_t data[];
} ObjForeign;

// A C-function which takes a Mochi closure as a callback is tricky to implement. This structure is
// also passed in where closures are expected so that the C-callback which calls the Mochi callback
// can remember where it was to call the Mochi callback properly.
typedef struct ForeignResume {
    Obj obj;
    MochiVM* vm;
    ObjFiber* fiber;
} ForeignResume;

typedef struct ObjList {
    Obj obj;
    Value elem;
    struct ObjList* next;
} ObjList;

typedef struct ObjArray {
    Obj obj;
    ValueBuffer elems;
} ObjArray;

typedef struct ObjSlice {
    Obj obj;
    int start;
    int count;
    ObjArray* source;
} ObjSlice;

typedef struct ObjByteArray {
    Obj obj;
    ByteBuffer elems;
} ObjByteArray;

typedef struct ObjByteSlice {
    Obj obj;
    int start;
    int count;
    ObjByteArray* source;
} ObjByteSlice;

typedef struct ObjRef {
    Obj obj;
    TableKey ptr;
} ObjRef;

typedef uint32_t StructId;

typedef struct ObjStruct {
    Obj obj;
    StructId id;
    int count;
    Value elems[];
} ObjStruct;

typedef struct ObjRecord {
    Obj obj;
    Table fields;
} ObjRecord;

typedef struct ObjVariant {
    Obj obj;
    TableKey label;
    int nesting;
    Value elem;
} ObjVariant;

// Creates a new fiber object with the values from the given initial stack.
ObjFiber* mochiNewFiber(MochiVM* vm, uint8_t* first, Value* initialStack, int initialStackCount);
ObjFiber* mochiFiberClone(MochiVM* vm, ObjFiber* orig);
static inline size_t mochiFiberValueCount(ObjFiber* fiber) {
    return fiber->valueStackTop - fiber->valueStack;
}
static inline size_t mochiFiberFrameCount(ObjFiber* fiber) {
    return fiber->frameStackTop - fiber->frameStack;
}
static inline size_t mochiFiberRootCount(ObjFiber* fiber) {
    return fiber->rootStackTop - fiber->rootStack;
}
static inline void mochiFiberPushValue(ObjFiber* fiber, Value v) {
    *fiber->valueStackTop++ = v;
}
static inline Value mochiFiberPopValue(ObjFiber* fiber) {
    return *(--fiber->valueStackTop);
}
static inline Value mochiFiberPeekValue(ObjFiber* fiber, int index) {
    return *(fiber->valueStackTop - index);
}
static inline void mochiFiberDropValues(ObjFiber* fiber, int count) {
    fiber->valueStackTop -= count;
}
static inline void mochiFiberPushFrame(ObjFiber* fiber, ObjVarFrame* frame) {
    *fiber->frameStackTop++ = frame;
}
static inline ObjVarFrame* mochiFiberPopFrame(ObjFiber* fiber) {
    return *(--fiber->frameStackTop);
}
static inline void mochiFiberPushRoot(ObjFiber* fiber, Obj* root) {
    *fiber->rootStackTop++ = root;
}
static inline Obj* mochiFiberPeekRoot(ObjFiber* fiber, int index) {
    return (*fiber->rootStackTop - index);
}
static inline Obj* mochiFiberPopRoot(ObjFiber* fiber) {
    return *(--fiber->rootStackTop);
}
static inline bool mochiFiberEqual(ObjFiber* left, ObjFiber* right) {
    return thrd_equal(left->thread, right->thread);
}

ObjClosure* mochiNewClosure(MochiVM* vm, uint8_t* body, uint8_t paramCount, uint16_t capturedCount);
void mochiClosureCapture(ObjClosure* closure, int captureIndex, Value value);

ObjContinuation* mochiNewContinuation(MochiVM* vm, uint8_t* resume, uint8_t paramCount, int savedStack,
                                      int savedFrames);

ObjVarFrame* newVarFrame(Value* vars, int varCount, MochiVM* vm);
ObjCallFrame* newCallFrame(Value* vars, int varCount, uint8_t* afterLocation, MochiVM* vm);
ObjHandleFrame* mochinewHandleFrame(MochiVM* vm, int handleId, uint8_t paramCount, uint8_t handlerCount,
                                    uint8_t* after);

ObjForeign* mochiNewForeign(MochiVM* vm, size_t size);
ObjCPointer* mochiNewCPointer(MochiVM* vm, void* pointer);
ForeignResume* mochiNewResume(MochiVM* vm, ObjFiber* fiber);

ObjRef* mochiNewRef(MochiVM* vm, TableKey ptr);

ObjStruct* mochiNewStruct(MochiVM* vm, StructId id, int elemCount);

ObjList* mochiListNil(MochiVM* vm);
ObjList* mochiListCons(MochiVM* vm, Value elem, ObjList* tail);
ObjList* mochiListTail(ObjList* list);
Value mochiListHead(ObjList* list);
int mochiListLength(ObjList* list);

ObjArray* mochiArrayNil(MochiVM* vm);
ObjArray* mochiArrayFill(MochiVM* vm, int amount, Value elem, ObjArray* array);
ObjArray* mochiArraySnoc(MochiVM* vm, Value elem, ObjArray* array);
Value mochiArrayGetAt(int index, ObjArray* array);
void mochiArraySetAt(int index, Value value, ObjArray* array);
int mochiArrayLength(ObjArray* array);
ObjArray* mochiArrayCopy(MochiVM* vm, int start, int length, ObjArray* array);

ObjSlice* mochiArraySlice(MochiVM* vm, int start, int length, ObjArray* array);
ObjSlice* mochiSubslice(MochiVM* vm, int start, int length, ObjSlice* slice);
Value mochiSliceGetAt(int index, ObjSlice* slice);
void mochiSliceSetAt(int index, Value value, ObjSlice* slice);
int mochiSliceLength(ObjSlice* slice);
ObjArray* mochiSliceCopy(MochiVM* vm, ObjSlice* slice);

ObjByteArray* mochiByteArrayNil(MochiVM* vm);
ObjByteArray* mochiByteArrayString(MochiVM* vm, const char* str);
ObjByteArray* mochiByteArrayFill(MochiVM* vm, int amount, uint8_t elem, ObjByteArray* array);
ObjByteArray* mochiByteArraySnoc(MochiVM* vm, uint8_t elem, ObjByteArray* array);
uint8_t mochiByteArrayGetAt(int index, ObjByteArray* array);
void mochiByteArraySetAt(int index, uint8_t value, ObjByteArray* array);
int mochiByteArrayLength(ObjByteArray* array);
ObjByteArray* mochiByteArrayCopy(MochiVM* vm, int start, int length, ObjByteArray* array);

ObjByteSlice* mochiByteArraySlice(MochiVM* vm, int start, int length, ObjByteArray* array);
ObjByteSlice* mochiByteSubslice(MochiVM* vm, int start, int length, ObjByteSlice* slice);
uint8_t mochiByteSliceGetAt(int index, ObjByteSlice* slice);
void mochiByteSliceSetAt(int index, uint8_t value, ObjByteSlice* slice);
int mochiByteSliceLength(ObjByteSlice* slice);
ObjByteArray* mochiByteSliceCopy(MochiVM* vm, ObjByteSlice* slice);

ObjRecord* mochiNewRecord(MochiVM* vm);
ObjRecord* mochiRecordExtend(MochiVM* vm, TableKey field, Value value, ObjRecord* rec);
ObjRecord* mochiRecordRestrict(MochiVM* vm, TableKey field, ObjRecord* rec);
ObjRecord* mochiRecordUpdate(MochiVM* vm, TableKey field, Value value, ObjRecord* rec);
Value mochiRecordSelect(TableKey field, ObjRecord* rec);

ObjVariant* mochiNewVariant(MochiVM* vm, TableKey label, Value elem);
ObjVariant* mochiVariantEmbed(MochiVM* vm, TableKey label, ObjVariant* variant);

void printObject(MochiVM* vm, Value object);

void mochiFreeObj(MochiVM* vm, Obj* object);

#endif