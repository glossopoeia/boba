#ifndef mochivm_value_ptr_union_h
#define mochivm_value_ptr_union_h

typedef struct {
    bool isHeap;
    union {
        bool boolean;
        int8_t i8;
        uint8_t u8;
        int16_t i16;
        uint16_t u16;
        int32_t i32;
        uint32_t u32;
        int64_t i64;
        uint64_t u64;
        float single;
        double dub;
        Obj* obj;
    } as;
} Value;

#define IS_OBJ(value)  ((value).isHeap)
#define IS_TINY(value) ((!(value).isHeap))

#define FALSE_VAL           ((Value){false, {.boolean = false}})
#define TRUE_VAL            ((Value){false, {.boolean = true}})
#define BOOL_VAL(vm, val)   ((val) ? TRUE_VAL : FALSE_VAL)
#define I8_VAL(vm, val)     ((Value){false, {.i8 = val}})
#define U8_VAL(vm, val)     ((Value){false, {.u8 = val}})
#define I16_VAL(vm, val)    ((Value){false, {.i16 = val}})
#define U16_VAL(vm, val)    ((Value){false, {.u16 = val}})
#define I32_VAL(vm, val)    ((Value){false, {.i32 = val}})
#define U32_VAL(vm, val)    ((Value){false, {.u32 = val}})
#define I64_VAL(vm, val)    ((Value){false, {.i64 = val}})
#define U64_VAL(vm, val)    ((Value){false, {.u64 = val}})
#define SINGLE_VAL(vm, val) ((Value){false, {.single = val}})
#define DOUBLE_VAL(vm, val) ((Value){false, {.dub = val}})

// Value -> 0 or 1.
#define AS_BOOL(value)   ((value).as.boolean)
#define AS_I8(value)     ((value).as.i8)
#define AS_U8(value)     ((value).as.u8)
#define AS_I16(value)    ((value).as.i16)
#define AS_U16(value)    ((value).as.u16)
#define AS_I32(value)    ((value).as.i32)
#define AS_U32(value)    ((value).as.u32)
#define AS_I64(value)    ((value).as.i64)
#define AS_U64(value)    ((value).as.u64)
#define AS_SINGLE(value) ((value).as.single)
#define AS_DOUBLE(value) ((value).as.dub)

// Value -> Obj*.
#define AS_OBJ(v) ((v).as.obj)

// Converts the raw object pointer [obj] to a [Value].
static inline Value mochiObjectToValue(Obj* obj) {
    Value value;
    value.isHeap = true;
    value.as.obj = obj;
    return value;
}

#endif