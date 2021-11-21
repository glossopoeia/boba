#ifndef mochivm_value_ptr_tagged_h
#define mochivm_value_ptr_tagged_h

typedef uint64_t Value;

#define PTR_MASK ((uint64_t)0xfffffffffffffffe)
#define TINY_TAG ((uint64_t)1)

#define IS_TINY(value) (((value)&TINY_TAG) == TINY_TAG)
#define IS_OBJ(value)  (((value)&TINY_TAG) == (uint64_t)0)

// A union to let us reinterpret a double as raw bits and back.
typedef union {
    uint64_t bits64;
    uint32_t bits32[2];
    float singles[2];
} MochiVMPointerBits;

static inline float mochiSingleFromBits(uint64_t bits) {
    MochiVMPointerBits data;
    data.bits64 = bits;
    return data.singles[1];
}

static inline uint64_t mochiSingleToBits(float single) {
    MochiVMPointerBits data;
    data.singles[0] = single;
    data.bits32[0] = TINY_TAG;
    return data.bits64;
}

#define FALSE_VAL           ((Value)TINY_TAG)
#define TRUE_VAL            ((Value)(uint64_t)(TINY_TAG | 2))
#define BOOL_VAL(vm, val)   ((val) ? TRUE_VAL : FALSE_VAL)
#define I8_VAL(vm, val)     ((Value)(uint64_t)(TINY_TAG | ((uint64_t)(val) << 56)))
#define U8_VAL(vm, val)     ((Value)(uint64_t)(TINY_TAG | ((uint64_t)(val) << 56)))
#define I16_VAL(vm, val)    ((Value)(uint64_t)(TINY_TAG | ((uint64_t)(val) << 48)))
#define U16_VAL(vm, val)    ((Value)(uint64_t)(TINY_TAG | ((uint64_t)(val) << 48)))
#define I32_VAL(vm, val)    ((Value)(uint64_t)(TINY_TAG | ((uint64_t)(val) << 32)))
#define U32_VAL(vm, val)    ((Value)(uint64_t)(TINY_TAG | ((uint64_t)(val) << 32)))
#define I64_VAL(vm, val)    (OBJ_VAL(mochiNewI64(vm, val)))
#define U64_VAL(vm, val)    (OBJ_VAL(mochiNewU64(vm, val)))
#define SINGLE_VAL(vm, val) (mochiSingleToBits(val))
#define DOUBLE_VAL(vm, val) (OBJ_VAL(mochiNewDouble(vm, val)))

#define AS_BOOL(value)   ((value) == TRUE_VAL)
#define AS_I8(value)     ((int8_t)(value >> 56))
#define AS_U8(value)     ((uint8_t)(value >> 56))
#define AS_I16(value)    ((int16_t)(value >> 48))
#define AS_U16(value)    ((uint16_t)(value >> 48))
#define AS_I32(value)    ((int32_t)(value >> 32))
#define AS_U32(value)    ((uint32_t)(value >> 32))
#define AS_I64(value)    (((ObjI64*)AS_OBJ(value))->val)
#define AS_U64(value)    (((ObjU64*)AS_OBJ(value))->val)
#define AS_SINGLE(value) (mochiSingleFromBits(value))
#define AS_DOUBLE(value) (((ObjDouble*)AS_OBJ(value))->val)

#define AS_OBJ(value) ((Obj*)(uintptr_t)((value)&PTR_MASK))

// Interprets [value] as a [double].
static inline double mochiValueToNum(Value value) {
    ASSERT(false, "mochiValueToNum not yet implemented for pointer tagging.");
    return 0;
}

// Converts [num] to a [Value].
static inline Value mochiNumToValue(double num) {
    ASSERT(false, "mochiNumToValue not yet implemented for pointer tagging.");
    return (Value)(uint64_t)0;
}

// Converts the raw object pointer [obj] to a [Value].
static inline Value mochiObjectToValue(Obj* obj) {
    // The triple casting is necessary here to satisfy some compilers:
    // 1. (uintptr_t) Convert the pointer to a number of the right size.
    // 2. (uint64_t)  Pad it up to 64 bits in 32-bit builds.
    // 3. Or in the bits to make a tagged NaN.
    // 4. Cast to a typedef'd value.
    return (Value)(PTR_MASK & (uint64_t)(uintptr_t)(obj));
}

#endif