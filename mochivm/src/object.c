#include <stdio.h>

#include "memory.h"
#include "object.h"
#include "vm.h"

static void initObj(MochiVM* vm, Obj* obj, ObjType type) {
    obj->type = type;
    obj->isMarked = false;
    // keep track of all allocated objects via the linked list in the vm
    obj->next = vm->objects;
    vm->objects = obj;
}

ObjI64* mochiNewI64(MochiVM* vm, int64_t val) {
    ObjI64* i = ALLOCATE(vm, ObjI64);
    initObj(vm, (Obj*)i, OBJ_I64);
    i->val = val;
    return i;
}

ObjU64* mochiNewU64(MochiVM* vm, uint64_t val) {
    ObjU64* i = ALLOCATE(vm, ObjU64);
    initObj(vm, (Obj*)i, OBJ_U64);
    i->val = val;
    return i;
}

ObjDouble* mochiNewDouble(MochiVM* vm, double val) {
    ObjDouble* i = ALLOCATE(vm, ObjDouble);
    initObj(vm, (Obj*)i, OBJ_DOUBLE);
    i->val = val;
    return i;
}

ObjVarFrame* newVarFrame(Value* vars, int varCount, MochiVM* vm) {
    ObjVarFrame* frame = ALLOCATE(vm, ObjVarFrame);
    initObj(vm, (Obj*)frame, OBJ_VAR_FRAME);
    frame->slots = vars;
    frame->slotCount = varCount;
    return frame;
}

ObjCallFrame* newCallFrame(Value* vars, int varCount, uint8_t* afterLocation, MochiVM* vm) {
    ObjCallFrame* frame = ALLOCATE(vm, ObjCallFrame);
    initObj(vm, (Obj*)frame, OBJ_CALL_FRAME);
    frame->vars.slots = vars;
    frame->vars.slotCount = varCount;
    frame->afterLocation = afterLocation;
    return frame;
}

ObjHandleFrame* mochinewHandleFrame(MochiVM* vm, int handleId, uint8_t paramCount, uint8_t handlerCount,
                                    uint8_t* after) {
    Value* params = ALLOCATE_ARRAY(vm, Value, paramCount);
    memset(params, 0, sizeof(Value) * paramCount);
    ObjClosure** handlers = ALLOCATE_ARRAY(vm, ObjClosure*, handlerCount);
    memset(handlers, 0, sizeof(ObjClosure*) * handlerCount);

    ObjHandleFrame* frame = ALLOCATE(vm, ObjHandleFrame);
    initObj(vm, (Obj*)frame, OBJ_HANDLE_FRAME);
    frame->call.vars.slots = params;
    frame->call.vars.slotCount = paramCount;
    frame->call.afterLocation = after;
    frame->handleId = handleId;
    frame->nesting = 0;
    frame->afterClosure = NULL;
    frame->handlers = handlers;
    frame->handlerCount = handlerCount;

    return frame;
}

ObjFiber* mochiNewFiber(MochiVM* vm, uint8_t* first, Value* initialStack, int initialStackCount) {
    // Allocate the arrays before the fiber in case it triggers a GC.
    Value* values = ALLOCATE_ARRAY(vm, Value, vm->config.valueStackCapacity);
    ObjVarFrame** frames = ALLOCATE_ARRAY(vm, ObjVarFrame*, vm->config.frameStackCapacity);
    Obj** roots = ALLOCATE_ARRAY(vm, Obj*, vm->config.rootStackCapacity);

    ObjFiber* fiber = ALLOCATE(vm, ObjFiber);
    initObj(vm, (Obj*)fiber, OBJ_FIBER);
    fiber->valueStack = values;
    fiber->valueStackTop = values;
    fiber->frameStack = frames;
    fiber->frameStackTop = frames;
    fiber->rootStack = roots;
    fiber->rootStackTop = roots;

    for (int i = 0; i < initialStackCount; i++) {
        values[i] = initialStack[i];
    }
    fiber->valueStackTop += initialStackCount;

    fiber->isSuspended = false;
    fiber->isRoot = false;
    fiber->caller = NULL;
    return fiber;
}

ObjClosure* mochiNewClosure(MochiVM* vm, uint8_t* body, uint8_t paramCount, uint16_t capturedCount) {
    ObjClosure* closure = ALLOCATE_FLEX(vm, ObjClosure, Value, capturedCount);
    initObj(vm, (Obj*)closure, OBJ_CLOSURE);
    closure->funcLocation = body;
    closure->paramCount = paramCount;
    closure->capturedCount = capturedCount;
    // Resume many is the default because multiple resumptions are the most general. Most closures
    // will not actually contain/perform continuation saving or restoring, this default is simply
    // provided so that the safest before for handler closures is assumed by default. Closures which
    // are not used as handlers will ignore this field anyway.
    closure->resumeLimit = RESUME_MANY;
    // reset the captured array in case there is a GC in between allocating and populating it
    memset(closure->captured, 0, sizeof(Value) * capturedCount);
    return closure;
}

void mochiClosureCapture(ObjClosure* closure, int captureIndex, Value value) {
    ASSERT(captureIndex < closure->capturedCount, "Closure capture index outside the bounds of the captured array");
    closure->captured[captureIndex] = value;
}

ObjContinuation* mochiNewContinuation(MochiVM* vm, uint8_t* resume, uint8_t paramCount, int savedStackCount,
                                      int savedFramesCount) {
    Value* savedStack = ALLOCATE_ARRAY(vm, Value, savedStackCount);
    memset(savedStack, 0, sizeof(Value) * savedStackCount);
    ObjVarFrame** savedFrames = ALLOCATE_ARRAY(vm, ObjVarFrame*, savedFramesCount);
    memset(savedFrames, 0, sizeof(ObjVarFrame*) * savedFramesCount);

    ObjContinuation* cont = ALLOCATE(vm, ObjContinuation);
    initObj(vm, (Obj*)cont, OBJ_CONTINUATION);
    cont->resumeLocation = resume;
    cont->paramCount = paramCount;
    cont->savedStack = savedStack;
    cont->savedFrames = savedFrames;
    cont->savedStackCount = savedStackCount;
    cont->savedFramesCount = savedFramesCount;
    return cont;
}

ObjForeign* mochiNewForeign(MochiVM* vm, size_t size) {
    ObjForeign* object = ALLOCATE_FLEX(vm, ObjForeign, uint8_t, size);
    initObj(vm, (Obj*)object, OBJ_FOREIGN);

    // Zero out the bytes.
    memset(object->data, 0, size);
    return object;
}

ObjCPointer* mochiNewCPointer(MochiVM* vm, void* pointer) {
    ObjCPointer* ptr = ALLOCATE(vm, ObjCPointer);
    initObj(vm, (Obj*)ptr, OBJ_C_POINTER);
    ptr->pointer = pointer;
    return ptr;
}

ForeignResume* mochiNewResume(MochiVM* vm, ObjFiber* fiber) {
    ForeignResume* res = ALLOCATE(vm, ForeignResume);
    initObj(vm, (Obj*)res, OBJ_FOREIGN_RESUME);
    res->vm = vm;
    res->fiber = fiber;
    return res;
}

ObjRef* mochiNewRef(MochiVM* vm, TableKey ptr) {
    ObjRef* ref = ALLOCATE(vm, ObjRef);
    initObj(vm, (Obj*)ref, OBJ_REF);
    ref->ptr = ptr;
    return ref;
}

ObjStruct* mochiNewStruct(MochiVM* vm, StructId id, int elemCount) {
    ObjStruct* stru = ALLOCATE_FLEX(vm, ObjStruct, Value, elemCount);
    initObj(vm, (Obj*)stru, OBJ_STRUCT);
    stru->id = id;
    stru->count = elemCount;
    return stru;
}

ObjList* mochiListNil(MochiVM* vm) {
    return NULL;
}

ObjList* mochiListCons(MochiVM* vm, Value elem, ObjList* tail) {
    ObjList* list = ALLOCATE(vm, ObjList);
    initObj(vm, (Obj*)list, OBJ_LIST);
    list->next = tail;
    list->elem = elem;
    return list;
}

ObjList* mochiListTail(ObjList* list) {
    return list->next;
}

Value mochiListHead(ObjList* list) {
    return list->elem;
}

int mochiListLength(ObjList* list) {
    int count = 0;
    while (list != NULL) {
        list = list->next;
        count++;
    }
    return count;
}

ObjArray* mochiArrayNil(MochiVM* vm) {
    ObjArray* arr = ALLOCATE(vm, ObjArray);
    initObj(vm, (Obj*)arr, OBJ_ARRAY);
    mochiValueBufferInit(&arr->elems);
    return arr;
}

ObjArray* mochiArrayFill(MochiVM* vm, int amount, Value elem, ObjArray* array) {
    mochiValueBufferFill(vm, &array->elems, elem, amount);
    return array;
}

ObjArray* mochiArraySnoc(MochiVM* vm, Value elem, ObjArray* array) {
    mochiValueBufferWrite(vm, &array->elems, elem);
    return array;
}

Value mochiArrayGetAt(int index, ObjArray* array) {
    ASSERT(array->elems.count > index, "Tried to access an element beyond the bounds of the Array.");
    return array->elems.data[index];
}

void mochiArraySetAt(int index, Value value, ObjArray* array) {
    ASSERT(array->elems.count > index, "Tried to modify an element beyond the bounds of the Array.");
    array->elems.data[index] = value;
}

int mochiArrayLength(ObjArray* array) {
    return array->elems.count;
}

ObjArray* mochiArrayCopy(MochiVM* vm, int start, int length, ObjArray* array) {
    ObjArray* copy = mochiArrayNil(vm);
    mochiFiberPushRoot(vm->fiber, (Obj*)copy);
    for (int i = 0; i < array->elems.count; i++) {
        mochiValueBufferWrite(vm, &copy->elems, array->elems.data[i]);
    }
    mochiFiberPopRoot(vm->fiber);
    return copy;
}

ObjSlice* mochiArraySlice(MochiVM* vm, int start, int length, ObjArray* array) {
    ASSERT(start + length <= array->elems.count,
           "Tried to creat a Slice that accesses elements beyond the length of the source Array.");
    ObjSlice* slice = ALLOCATE(vm, ObjSlice);
    initObj(vm, (Obj*)slice, OBJ_SLICE);
    slice->start = start;
    slice->count = length;
    slice->source = array;
    return slice;
}

ObjSlice* mochiSubslice(MochiVM* vm, int start, int length, ObjSlice* slice) {
    return mochiArraySlice(vm, start + slice->start, length, slice->source);
}

Value mochiSliceGetAt(int index, ObjSlice* slice) {
    ASSERT(slice->count > index, "Tried to access an element beyond the bounds of the Slice.");
    return slice->source->elems.data[slice->start + index];
}

void mochiSliceSetAt(int index, Value value, ObjSlice* slice) {
    ASSERT(slice->count > index, "Tried to modify an element beyond the bounds of the Slice.");
    slice->source->elems.data[slice->start + index] = value;
}

int mochiSliceLength(ObjSlice* slice) {
    return slice->count;
}

ObjArray* mochiSliceCopy(MochiVM* vm, ObjSlice* slice) {
    ObjArray* copy = mochiArrayNil(vm);
    mochiFiberPushRoot(vm->fiber, (Obj*)copy);
    for (int i = 0; i < slice->count; i++) {
        mochiValueBufferWrite(vm, &copy->elems, slice->source->elems.data[i]);
    }
    mochiFiberPopRoot(vm->fiber);
    return copy;
}

ObjByteArray* mochiByteArrayNil(MochiVM* vm) {
    ObjByteArray* arr = ALLOCATE(vm, ObjByteArray);
    initObj(vm, (Obj*)arr, OBJ_BYTE_ARRAY);
    mochiByteBufferInit(&arr->elems);
    return arr;
}

ObjByteArray* mochiByteArrayString(MochiVM* vm, const char* string) {
    ObjByteArray* str = mochiByteArrayNil(vm);
    mochiFiberPushRoot(vm->fiber, (Obj*)str);
    int i = 0;
    while (string[i] != '\0') {
        mochiByteArraySnoc(vm, string[i], str);
        i++;
    }
    mochiByteArraySnoc(vm, '\0', str);
    mochiFiberPopRoot(vm->fiber);
    return str;
}

ObjByteArray* mochiByteArrayFill(MochiVM* vm, int amount, uint8_t elem, ObjByteArray* array) {
    mochiByteBufferFill(vm, &array->elems, elem, amount);
    return array;
}

ObjByteArray* mochiByteArraySnoc(MochiVM* vm, uint8_t elem, ObjByteArray* array) {
    mochiByteBufferWrite(vm, &array->elems, elem);
    return array;
}

uint8_t mochiByteArrayGetAt(int index, ObjByteArray* array) {
    ASSERT(array->elems.count > index, "Tried to access an element beyond the bounds of the Array.");
    return array->elems.data[index];
}

void mochiByteArraySetAt(int index, uint8_t value, ObjByteArray* array) {
    ASSERT(array->elems.count > index, "Tried to modify an element beyond the bounds of the Array.");
    array->elems.data[index] = value;
}

int mochiByteArrayLength(ObjByteArray* array) {
    return array->elems.count;
}

ObjByteArray* mochiByteArrayCopy(MochiVM* vm, int start, int length, ObjByteArray* array) {
    ObjByteArray* copy = mochiByteArrayNil(vm);
    mochiFiberPushRoot(vm->fiber, (Obj*)copy);
    for (int i = 0; i < array->elems.count; i++) {
        mochiByteBufferWrite(vm, &copy->elems, array->elems.data[i]);
    }
    mochiFiberPopRoot(vm->fiber);
    return copy;
}

ObjByteSlice* mochiByteArraySlice(MochiVM* vm, int start, int length, ObjByteArray* array) {
    ASSERT(start + length <= array->elems.count,
           "Tried to creat a Slice that accesses elements beyond the length of the source Array.");
    ObjByteSlice* slice = ALLOCATE(vm, ObjByteSlice);
    initObj(vm, (Obj*)slice, OBJ_BYTE_SLICE);
    slice->start = start;
    slice->count = length;
    slice->source = array;
    return slice;
}

ObjByteSlice* mochiByteSubslice(MochiVM* vm, int start, int length, ObjByteSlice* slice) {
    return mochiByteArraySlice(vm, start + slice->start, length, slice->source);
}

uint8_t mochiByteSliceGetAt(int index, ObjByteSlice* slice) {
    ASSERT(slice->count > index, "Tried to access an element beyond the bounds of the Slice.");
    return slice->source->elems.data[slice->start + index];
}

void mochiByteSliceSetAt(int index, uint8_t value, ObjByteSlice* slice) {
    ASSERT(slice->count > index, "Tried to modify an element beyond the bounds of the Slice.");
    slice->source->elems.data[slice->start + index] = value;
}

int mochiByteSliceLength(ObjByteSlice* slice) {
    return slice->count;
}

ObjByteArray* mochiByteSliceCopy(MochiVM* vm, ObjByteSlice* slice) {
    ObjByteArray* copy = mochiByteArrayNil(vm);
    mochiFiberPushRoot(vm->fiber, (Obj*)copy);
    for (int i = 0; i < slice->count; i++) {
        mochiByteBufferWrite(vm, &copy->elems, slice->source->elems.data[i]);
    }
    mochiFiberPopRoot(vm->fiber);
    return copy;
}

ObjRecord* mochiNewRecord(MochiVM* vm) {
    ObjRecord* rec = ALLOCATE(vm, ObjRecord);
    initObj(vm, (Obj*)rec, OBJ_RECORD);
    mochiTableInit(&rec->fields);
    return rec;
}

ObjRecord* mochiRecordExtend(MochiVM* vm, TableKey field, Value value, ObjRecord* rec) {
    Table* fields = mochiTableClone(vm, &rec->fields, true);
    ObjRecord* cloned = mochiNewRecord(vm);
    cloned->fields = *fields;
    mochiFiberPushRoot(vm->fiber, (Obj*)cloned);
    DEALLOCATE(vm, fields);
    mochiTableSetScoped(vm, &cloned->fields, field, value);
    mochiFiberPopRoot(vm->fiber);
    return cloned;
}

ObjRecord* mochiRecordRestrict(MochiVM* vm, TableKey field, ObjRecord* rec) {
    Table* fields = mochiTableClone(vm, &rec->fields, true);
    ObjRecord* cloned = mochiNewRecord(vm);
    cloned->fields = *fields;
    mochiFiberPushRoot(vm->fiber, (Obj*)cloned);
    DEALLOCATE(vm, fields);
    mochiTableTryRemoveScoped(vm, &cloned->fields, field);
    mochiFiberPopRoot(vm->fiber);
    return cloned;
}

ObjRecord* mochiRecordUpdate(MochiVM* vm, TableKey field, Value value, ObjRecord* rec) {
    // TODO: this does two objects allocations, make it just do one
    ObjRecord* restr = mochiRecordRestrict(vm, field, rec);
    mochiFiberPushRoot(vm->fiber, (Obj*)restr);
    ObjRecord* upd = mochiRecordExtend(vm, field, value, restr);
    mochiFiberPopRoot(vm->fiber);
    return upd;
}

Value mochiRecordSelect(TableKey field, ObjRecord* rec) {
    Value val;
    if (mochiTableGet(&rec->fields, field, &val)) {
        return val;
    }
    ASSERT(false, "Record does not contain field for selection.");
    return FALSE_VAL;
}

ObjVariant* mochiNewVariant(MochiVM* vm, TableKey label, Value elem) {
    ObjVariant* var = ALLOCATE(vm, ObjVariant);
    initObj(vm, (Obj*)var, OBJ_VARIANT);
    var->label = label;
    var->nesting = 0;
    var->elem = elem;
    return var;
}

ObjVariant* mochiVariantEmbed(MochiVM* vm, TableKey label, ObjVariant* var) {
    ObjVariant* cloned = mochiNewVariant(vm, var->label, var->elem);
    cloned->nesting = var->nesting;
    if (label == cloned->label) {
        cloned->nesting += 1;
    }
    return cloned;
}

static void freeVarFrame(MochiVM* vm, ObjVarFrame* frame) {
    DEALLOCATE(vm, frame->slots);
}

void mochiFreeObj(MochiVM* vm, Obj* object) {

#if MOCHIVM_DEBUG_TRACE_MEMORY
    printf("free ");
    printValue(vm, OBJ_VAL(object));
    printf(" @ %p\n", object);
#endif

    switch (object->type) {
    case OBJ_VAR_FRAME: {
        freeVarFrame(vm, (ObjVarFrame*)object);
        break;
    }
    case OBJ_CALL_FRAME: {
        freeVarFrame(vm, (ObjVarFrame*)object);
        break;
    }
    case OBJ_HANDLE_FRAME: {
        freeVarFrame(vm, (ObjVarFrame*)object);
        ObjHandleFrame* handle = (ObjHandleFrame*)object;
        DEALLOCATE(vm, handle->handlers);
        break;
    }
    case OBJ_CONTINUATION: {
        ObjContinuation* cont = (ObjContinuation*)object;
        DEALLOCATE(vm, cont->savedStack);
        DEALLOCATE(vm, cont->savedFrames);
        break;
    }
    case OBJ_FIBER: {
        ObjFiber* fiber = (ObjFiber*)object;
        DEALLOCATE(vm, fiber->valueStack);
        DEALLOCATE(vm, fiber->frameStack);
        DEALLOCATE(vm, fiber->rootStack);
        break;
    }
    case OBJ_ARRAY: {
        ObjArray* arr = (ObjArray*)object;
        mochiValueBufferClear(vm, &arr->elems);
        break;
    }
    case OBJ_BYTE_ARRAY: {
        ObjByteArray* arr = (ObjByteArray*)object;
        mochiByteBufferClear(vm, &arr->elems);
        break;
    }
    case OBJ_REF: {
        ObjRef* ref = (ObjRef*)object;
        // NOTE: this assumes garbage collection, i.e. there are
        // no other ObjRef instances that contain the same ptr value
        // that ref contains. If the ref can be fully copied into
        // a new ObjRef with the same ptr value, the following is
        // no longer valid. But note that this is not the same as
        // having multiple pointers to ref on the value/frame stack,
        // which is perfectly fine since the table-clearing logic will
        // only occur when ref becomes fully unreachable.
        mochiTableTryRemove(vm, &vm->heap, ref->ptr);
        break;
    }
    case OBJ_RECORD: {
        ObjRecord* rec = (ObjRecord*)object;
        mochiTableClear(vm, &rec->fields);
        break;
    }
    case OBJ_CLOSURE:
        break;
    case OBJ_FOREIGN:
        break;
    case OBJ_C_POINTER:
        break;
    case OBJ_LIST:
        break;
    case OBJ_FOREIGN_RESUME:
        break;
    case OBJ_SLICE:
        break;
    case OBJ_BYTE_SLICE:
        break;
    case OBJ_STRUCT:
        break;
    case OBJ_VARIANT:
        break;
    case OBJ_I64:
        break;
    case OBJ_U64:
        break;
    case OBJ_DOUBLE:
        break;
    }

    DEALLOCATE(vm, object);
}

void printObject(MochiVM* vm, Value object) {
    if (AS_OBJ(object) == NULL) {
        printf("nil");
        return;
    }

    switch (AS_OBJ(object)->type) {
    case OBJ_I64: {
        ObjI64* i = (ObjI64*)AS_OBJ(object);
        printf("%jd", i->val);
        break;
    }
    case OBJ_U64: {
        ObjU64* i = (ObjU64*)AS_OBJ(object);
        printf("%ju", i->val);
        break;
    }
    case OBJ_DOUBLE: {
        ObjDouble* i = (ObjDouble*)AS_OBJ(object);
        printf("%f", i->val);
        break;
    }
    case OBJ_VAR_FRAME: {
        ObjVarFrame* frame = AS_VAR_FRAME(object);
        printf("var(%d)", frame->slotCount);
        break;
    }
    case OBJ_CALL_FRAME: {
        ObjCallFrame* frame = AS_CALL_FRAME(object);
        printf("call(%d -> %ld)", frame->vars.slotCount, frame->afterLocation - vm->code.data);
        break;
    }
    case OBJ_HANDLE_FRAME: {
        ObjHandleFrame* frame = AS_HANDLE_FRAME(object);
        printf("handle(%d: n(%d) %d %d -> %ld)", frame->handleId, frame->nesting, frame->handlerCount,
               frame->call.vars.slotCount, frame->call.afterLocation - vm->code.data);
        break;
    }
    case OBJ_CLOSURE: {
        ObjClosure* closure = AS_CLOSURE(object);
        printf("closure(%d: %d -> %ld)", closure->capturedCount, closure->paramCount,
               closure->funcLocation - vm->code.data);
        break;
    }
    case OBJ_CONTINUATION: {
        ObjContinuation* cont = AS_CONTINUATION(object);
        printf("continuation(%d: v(%d) f(%d) -> %ld)", cont->paramCount, cont->savedStackCount, cont->savedFramesCount,
               cont->resumeLocation - vm->code.data);
        break;
    }
    case OBJ_FIBER: {
        printf("fiber");
        break;
    }
    case OBJ_FOREIGN: {
        printf("foreign");
        break;
    }
    case OBJ_C_POINTER: {
        printf("c_ptr");
        break;
    }
    case OBJ_LIST: {
        ObjList* list = AS_LIST(object);
        printf("cons(");
        printValue(vm, list->elem);
        printf(",");
        printObject(vm, OBJ_VAL(list->next));
        printf(")");
        break;
    }
    case OBJ_ARRAY: {
        ObjArray* arr = AS_ARRAY(object);
        printf("arr(");
        for (int i = 0; i < arr->elems.count; i++) {
            printValue(vm, arr->elems.data[i]);
            if (i < arr->elems.count - 1) {
                printf(",");
            }
        }
        printf(")");
        break;
    }
    case OBJ_SLICE: {
        ObjSlice* slice = AS_SLICE(object);
        printf("slice(");
        for (int i = 0; i < slice->count; i++) {
            printValue(vm, slice->source->elems.data[slice->start + i]);
            if (i < slice->count - 1) {
                printf(",");
            }
        }
        printf(")");
        break;
    }
    case OBJ_BYTE_ARRAY: {
        ObjByteArray* arr = AS_BYTE_ARRAY(object);
        printf("barray(");
        for (int i = 0; i < arr->elems.count; i++) {
            printf("%d", arr->elems.data[i]);
            if (i < arr->elems.count - 1) {
                printf(",");
            }
        }
        printf(")");
        break;
    }
    case OBJ_BYTE_SLICE: {
        ObjByteSlice* slice = AS_BYTE_SLICE(object);
        printf("bslice(");
        for (int i = 0; i < slice->count; i++) {
            printf("%d", slice->source->elems.data[slice->start + i]);
            if (i < slice->count - 1) {
                printf(",");
            }
        }
        printf(")");
        break;
    }
    case OBJ_FOREIGN_RESUME: {
        printf("foreign_resume");
        break;
    }
    case OBJ_REF: {
        printf("ref(");
        ObjRef* ref = AS_REF(object);
        Value val;
        if (mochiTableGet(&vm->heap, ref->ptr, &val)) {
            printValue(vm, val);
        } else {
            printf("NOT_FOUND");
        }
        printf(")");
        break;
    }
    case OBJ_STRUCT: {
        printf("struct(");
        ObjStruct* stru = AS_STRUCT(object);
        for (int i = 0; i < stru->count; i++) {
            printValue(vm, stru->elems[i]);
            if (i < stru->count - 1) {
                printf(",");
            }
        }
        printf(")");
        break;
    }
    case OBJ_RECORD: {
        printf("record(not-yet-implemented)");
        break;
    }
    case OBJ_VARIANT: {
        ObjVariant* variant = AS_VARIANT(object);
        printf("variant(%ld +%d -- ", variant->label, variant->nesting);
        printValue(vm, variant->elem);
        printf(")");
        break;
    }
    default: {
        printf("unknown(%d)", AS_OBJ(object)->type);
        break;
    }
    }
}