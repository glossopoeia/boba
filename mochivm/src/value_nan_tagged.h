#ifndef mochivm_value_nan_tagged_h
#define mochivm_value_nan_tagged_h

// An IEEE 754 double-precision float is a 64-bit value with bits laid out like:
//
// 1 Sign bit
// | 11 Exponent bits
// | |          52 Mantissa (i.e. fraction) bits
// | |          |
// S[Exponent-][Mantissa------------------------------------------]
//
// The details of how these are used to represent numbers aren't really
// relevant here as long we don't interfere with them. The important bit is NaN.
//
// An IEEE double can represent a few magical values like NaN ("not a number"),
// Infinity, and -Infinity. A NaN is any value where all exponent bits are set:
//
//  v--NaN bits
// -11111111111----------------------------------------------------
//
// Here, "-" means "doesn't matter". Any bit sequence that matches the above is
// a NaN. With all of those "-", it obvious there are a *lot* of different
// bit patterns that all mean the same thing. NaN tagging takes advantage of
// this. We'll use those available bit patterns to represent things other than
// numbers without giving up any valid numeric values.
//
// NaN values come in two flavors: "signalling" and "quiet". The former are
// intended to halt execution, while the latter just flow through arithmetic
// operations silently. We want the latter. Quiet NaNs are indicated by setting
// the highest mantissa bit:
//
//             v--Highest mantissa bit
// -[NaN      ]1---------------------------------------------------
//
// If all of the NaN bits are set, it's not a number. Otherwise, it is.
// That leaves all of the remaining bits as available for us to play with. We
// stuff a few different kinds of things here: special singleton values like
// "true", "false", and pointers to objects allocated on the heap.
// We'll use the sign bit to distinguish non-double values from pointers. If
// it's set, it's a pointer.
//
// v--Pointer or non-double?
// S[NaN      ]1---------------------------------------------------
//
// For non-double values, we store 32 bit values in the lower bits of the double.
//
// For pointers, we are left with 51 bits of mantissa to store an address.
// That's more than enough room for a 32-bit address. Even 64-bit machines
// only actually use 48 bits for addresses, so we've got plenty. We just stuff
// the address right into the mantissa.
//
// Ta-da, double precision numbers, pointers, and non-double values,
// all stuffed into a single 64-bit sequence. Even better, we don't have to
// do any masking or work to extract number values: they are unmodified. This
// means math on doubles is fast.
typedef uint64_t Value;

// A union to let us reinterpret a double as raw bits and back.
typedef union {
    uint64_t bits64;
    uint32_t bits32[2];
    float singles[2];
    double dub;
} MochiVMDoubleBits;

#define MOCHIVM_DOUBLE_QNAN_POS_MIN_BITS (UINT64_C(0x7FF8000000000000))
#define MOCHIVM_DOUBLE_QNAN_POS_MAX_BITS (UINT64_C(0x7FFFFFFFFFFFFFFF))

#define MOCHIVM_DOUBLE_NAN (mochiDoubleFromBits(MOCHIVM_DOUBLE_QNAN_POS_MIN_BITS))

// A mask that selects the sign bit.
#define SIGN_BIT ((uint64_t)1 << 63)

// The bits that must be set to indicate a quiet NaN.
#define QNAN  ((uint64_t)0x7ffc000000000000)
#define LOW8  ((uint64_t)0x00000000000000ff)
#define LOW16 ((uint64_t)0x000000000000ffff)
#define LOW32 ((uint64_t)0x00000000ffffffff)

static inline double mochiDoubleFromBits(uint64_t bits) {
    MochiVMDoubleBits data;
    data.bits64 = bits;
    return data.dub;
}

static inline float mochiSingleFromBits(uint64_t bits) {
    MochiVMDoubleBits data;
    data.bits64 = bits;
    return data.singles[1];
}

static inline uint64_t mochiDoubleToBits(double dub) {
    MochiVMDoubleBits data;
    data.dub = dub;
    return data.bits64;
}

static inline uint64_t mochiSingleToBits(float single) {
    MochiVMDoubleBits data;
    data.singles[1] = single;
    data.bits32[0] = (uint32_t)(QNAN >> 32);
    return data.bits64;
}

// An object pointer is a NaN with a set sign bit.
#define IS_OBJ(value)  (((value) & (QNAN | SIGN_BIT)) == (QNAN | SIGN_BIT))
#define IS_TINY(value) (!IS_OBJ(value))

#define FALSE_VAL           ((Value)(uint64_t)(QNAN | 0))
#define TRUE_VAL            ((Value)(uint64_t)(QNAN | 1))
#define BOOL_VAL(vm, val)   ((val) ? TRUE_VAL : FALSE_VAL)
#define I8_VAL(vm, val)     ((Value)(uint64_t)(QNAN | (val)))
#define U8_VAL(vm, val)     ((Value)(uint64_t)(QNAN | (val)))
#define I16_VAL(vm, val)    ((Value)(uint64_t)(QNAN | (val)))
#define U16_VAL(vm, val)    ((Value)(uint64_t)(QNAN | (val)))
#define I32_VAL(vm, val)    ((Value)(uint64_t)(QNAN | (val)))
#define U32_VAL(vm, val)    ((Value)(uint64_t)(QNAN | (val)))
#define I64_VAL(vm, val)    (OBJ_VAL(mochiNewI64(vm, val)))
#define U64_VAL(vm, val)    (OBJ_VAL(mochiNewU64(vm, val)))
#define SINGLE_VAL(vm, val) (mochiSingleToBits(val))
#define DOUBLE_VAL(vm, val) (mochiDoubleToBits(val))

// Value -> 0 or 1.
#define AS_BOOL(value)   ((value) == TRUE_VAL)
#define AS_I8(value)     ((int8_t)((value)&LOW8))
#define AS_U8(value)     ((uint8_t)((value)&LOW8))
#define AS_I16(value)    ((int16_t)((value)&LOW16))
#define AS_U16(value)    ((uint16_t)((value)&LOW16))
#define AS_I32(value)    ((int32_t)((value)&LOW32))
#define AS_U32(value)    ((uint32_t)((value)&LOW32))
#define AS_I64(value)    (((ObjI64*)AS_OBJ(value))->val)
#define AS_U64(value)    (((ObjU64*)AS_OBJ(value))->val)
#define AS_SINGLE(value) (mochiSingleFromBits(value))
#define AS_DOUBLE(value) (mochiDoubleFromBits(value))

// Value -> Obj*.
#define AS_OBJ(value) ((Obj*)(uintptr_t)((value) & ~(SIGN_BIT | QNAN)))

// Converts the raw object pointer [obj] to a [Value].
static inline Value mochiObjectToValue(Obj* obj) {
    // The triple casting is necessary here to satisfy some compilers:
    // 1. (uintptr_t) Convert the pointer to a number of the right size.
    // 2. (uint64_t)  Pad it up to 64 bits in 32-bit builds.
    // 3. Or in the bits to make a tagged NaN.
    // 4. Cast to a typedef'd value.
    return (Value)(SIGN_BIT | QNAN | (uint64_t)(uintptr_t)(obj));
}

#endif