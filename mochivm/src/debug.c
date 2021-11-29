#include <stdio.h>

#include "debug.h"

static short getShort(uint8_t* buffer, int offset) {
    return (buffer[offset] << 8) | buffer[offset + 1];
}

static uint16_t getUShort(uint8_t* buffer, int offset) {
    return (uint16_t)((buffer[offset] << 8) | buffer[offset + 1]);
}

static int getInt(uint8_t* buffer, int offset) {
    return (buffer[offset] << 24) | (buffer[offset + 1] << 16) | (buffer[offset + 2] << 8) | buffer[offset + 3];
}

static uint32_t getUInt(uint8_t* buffer, int offset) {
    return (buffer[offset] << 24) | (buffer[offset + 1] << 16) | (buffer[offset + 2] << 8) | buffer[offset + 3];
}

static int64_t getLong(uint8_t* buffer, int offset) {
    return ((uint64_t)buffer[offset] << 56) | ((uint64_t)buffer[offset + 1] << 48) | ((uint64_t)buffer[offset + 2] << 40) | ((uint64_t)buffer[offset + 3] << 32)
        | (buffer[offset + 4] << 24) | (buffer[offset + 5] << 16) | (buffer[offset + 6] << 8) | buffer[offset + 7];
}

static uint64_t getULong(uint8_t* buffer, int offset) {
    return ((uint64_t)buffer[offset] << 56) | ((uint64_t)buffer[offset + 1] << 48) | ((uint64_t)buffer[offset + 2] << 40) | ((uint64_t)buffer[offset + 3] << 32)
        | (buffer[offset + 4] << 24) | (buffer[offset + 5] << 16) | (buffer[offset + 6] << 8) | buffer[offset + 7];
}

// Easy function to print out 1-byte instructions and return the new offset.
static int simpleInstruction(const char* name, int offset) {
    printf("%s\n", name);
    return offset + 1;
}

static int sbyteArgInstruction(const char* name, MochiVM* vm, int offset) {
    printf("%-16s %d\n", name, vm->code.data[offset + 1]);
    return offset + 2;
}

static int byteArgInstruction(const char* name, MochiVM* vm, int offset) {
    printf("%-16s %u\n", name, vm->code.data[offset + 1]);
    return offset + 2;
}

static int shortArgInstruction(const char* name, MochiVM* vm, int offset) {
    uint8_t* code = vm->code.data;
    printf("%-16s %d\n", name, getShort(code, offset + 1));
    return offset + 3;
}

static int ushortArgInstruction(const char* name, MochiVM* vm, int offset) {
    uint8_t* code = vm->code.data;
    printf("%-16s %u\n", name, getUShort(code, offset + 1));
    return offset + 3;
}

static int intArgInstruction(const char* name, MochiVM* vm, int offset) {
    uint8_t* code = vm->code.data;
    printf("%-16s %d\n", name, getInt(code, offset + 1));
    return offset + 5;
}

static int uintArgInstruction(const char* name, MochiVM* vm, int offset) {
    uint8_t* code = vm->code.data;
    printf("%-16s %u\n", name, getUInt(code, offset + 1));
    return offset + 5;
}

static int longArgInstruction(const char* name, MochiVM* vm, int offset) {
    uint8_t* code = vm->code.data;
    printf("%-16s %ld\n", name, getLong(code, offset + 1));
    return offset + 9;
}

static int ulongArgInstruction(const char* name, MochiVM* vm, int offset) {
    uint8_t* code = vm->code.data;
    printf("%-16s %lu\n", name, getULong(code, offset + 1));
    return offset + 9;
}

static int singleArgInstruction(const char* name, MochiVM* vm, int offset) {
    uint8_t* code = vm->code.data;
    union {
        float a;
        unsigned char b[4];
    } reinterpret;
    memcpy(&reinterpret, code + offset + 1, sizeof(unsigned char) * 4);
    printf("%-16s %f\n", name, reinterpret.a);
    return offset + 5;
}

static int doubleArgInstruction(const char* name, MochiVM* vm, int offset) {
    uint8_t* code = vm->code.data;
    union {
        double a;
        unsigned char b[8];
    } reinterpret;
    memcpy(&reinterpret, code + offset + 1, sizeof(unsigned char) * 8);
    printf("%-16s %f\n", name, reinterpret.a);
    return offset + 9;
}

static int twoIntArgInstruction(const char* name, MochiVM* vm, int offset) {
    uint8_t* code = vm->code.data;
    offset += 1;

    int argOne = getInt(code, offset);
    offset += 4;
    int argTwo = getInt(code, offset);
    offset += 4;
    printf("%-16s %-8d %-8d\n", name, argOne, argTwo);
    return offset;
}

static int callInstruction(const char* name, MochiVM* vm, int offset) {
    uint8_t* code = vm->code.data;
    int instrIndex = getInt(code, offset + 1);
    const char* str = mochiGetLabel(vm, instrIndex);
    if (str == NULL) {
        printf("%-16s %d\n", name, instrIndex);
    } else {
        printf("%-16s %s\n", name, str);
    }
    return offset + 5;
}

static int constantInstruction(const char* name, MochiVM* vm, int offset) {
    uint8_t* code = vm->code.data;
    uint16_t constant = getShort(code, offset + 1);
    ASSERT(constant < vm->constants.count,
           "Cannot write CONSTANT instruction because the constant index was less than the constant pool size.");
    printf("%-16s %-4d '", name, constant);
    printValue(vm, vm->constants.data[constant]);
    printf("'\n");
    return offset + 3;
}

static int closureInstruction(const char* name, MochiVM* vm, int offset) {
    uint8_t* code = vm->code.data;
    offset += 1;

    int body = getInt(code, offset);
    offset += 4;
    const char* str = mochiGetLabel(vm, body);
    uint8_t paramCount = code[offset];
    offset += 1;
    uint16_t captureCount = getUShort(code, offset);
    offset += 2;

    if (str == NULL) {
        printf("%-16s %-8d %-3d %-5d ( ", name, body, paramCount, captureCount);
    } else {
        printf("%-16s %s %-3d %-5d ( ", name, str, paramCount, captureCount);
    }
    for (int i = 0; i < captureCount; i++) {
        printf("%5d:%5d ", getShort(code, offset + i * 4), getShort(code, offset + 2 + i * 4));
    }
    printf(")\n");
    return offset + captureCount * 4;
}

static int actionInstruction(const char* name, MochiVM* vm, int offset) {
    uint8_t* code = vm->code.data;
    offset += 1;

    int handleId = getInt(code, offset);
    offset += 4;
    int handlerId = code[offset];
    offset += 1;
    printf("%-16s %-8d %-3d\n", name, handleId, handlerId);
    return offset;
}

void disassembleChunk(MochiVM* vm, const char* name) {
    printf("== begin: %s ==\n", name);

    for (int offset = 0; offset < vm->code.count;) {
        // recall that instructions can be different size, hence not simply incrementing here
        offset = disassembleInstruction(vm, offset);
    }

    printf("== end: %s ==\n", name);
}

int disassembleInstruction(MochiVM* vm, int offset) {
    printf("%04d ", offset);
    if (offset > 0 && vm->lines.data[offset] == vm->lines.data[offset - 1]) {
        printf("   | ");
    } else {
        printf("%4d ", vm->lines.data[offset]);
    }

    uint8_t instruction = vm->code.data[offset];
    switch (instruction) {
    case CODE_NOP:
        return simpleInstruction("NOP", offset);
    case CODE_BREAKPOINT:
        return simpleInstruction("BREAKPOINT", offset);
    case CODE_ABORT:
        return byteArgInstruction("ABORT", vm, offset);
    case CODE_CONSTANT:
        return constantInstruction("CONSTANT", vm, offset);
    case CODE_PERM_QUERY:
        return shortArgInstruction("PERM_QUERY", vm, offset);
    case CODE_PERM_REQUEST:
        return shortArgInstruction("PERM_REQUEST", vm, offset);
    case CODE_PERM_REQUEST_ALL:
        return shortArgInstruction("PERM_REQUEST_ALL", vm, offset);
    case CODE_PERM_REVOKE:
        return shortArgInstruction("PERM_REVOKE", vm, offset);
    case CODE_TRUE:
        return simpleInstruction("TRUE", offset);
    case CODE_FALSE:
        return simpleInstruction("FALSE", offset);
    case CODE_BOOL_NOT:
        return simpleInstruction("BOOL_NOT", offset);
    case CODE_BOOL_AND:
        return simpleInstruction("BOOL_AND", offset);
    case CODE_BOOL_OR:
        return simpleInstruction("BOOL_OR", offset);
    case CODE_BOOL_NEQ:
        return simpleInstruction("BOOL_NEQ", offset);
    case CODE_BOOL_EQ:
        return simpleInstruction("BOOL_EQ", offset);
    case CODE_I8:
        return sbyteArgInstruction("I8", vm, offset);
    case CODE_U8:
        return byteArgInstruction("U8", vm, offset);
    case CODE_I16:
        return shortArgInstruction("I16", vm, offset);
    case CODE_U16:
        return ushortArgInstruction("U16", vm, offset);
    case CODE_I32:
        return intArgInstruction("I32", vm, offset);
    case CODE_U32:
        return uintArgInstruction("U32", vm, offset);
    case CODE_I64:
        return longArgInstruction("I64", vm, offset);
    case CODE_U64:
        return ulongArgInstruction("U64", vm, offset);
    case CODE_SINGLE:
        return singleArgInstruction("SINGLE", vm, offset);
    case CODE_DOUBLE:
        return doubleArgInstruction("DOUBLE", vm, offset);
    case CODE_INT_NEG:
        return byteArgInstruction("INT_NEG", vm, offset);
    case CODE_INT_INC:
        return byteArgInstruction("INT_INC", vm, offset);
    case CODE_INT_DEC:
        return byteArgInstruction("INT_DEC", vm, offset);
    case CODE_INT_ADD:
        return byteArgInstruction("INT_ADD", vm, offset);
    case CODE_INT_SUB:
        return byteArgInstruction("INT_SUB", vm, offset);
    case CODE_INT_MUL:
        return byteArgInstruction("INT_MUL", vm, offset);
    case CODE_INT_DIV_REM_T:
        return byteArgInstruction("INT_DIV_REM_T", vm, offset);
    case CODE_INT_DIV_REM_F:
        return byteArgInstruction("INT_DIV_REM_F", vm, offset);
    case CODE_INT_DIV_REM_E:
        return byteArgInstruction("INT_DIV_REM_E", vm, offset);
    case CODE_INT_OR:
        return byteArgInstruction("INT_OR", vm, offset);
    case CODE_INT_AND:
        return byteArgInstruction("INT_AND", vm, offset);
    case CODE_INT_XOR:
        return byteArgInstruction("INT_XOR", vm, offset);
    case CODE_INT_COMP:
        return byteArgInstruction("INT_COMP", vm, offset);
    case CODE_INT_SHL:
        return byteArgInstruction("INT_SHL", vm, offset);
    case CODE_INT_SHR:
        return byteArgInstruction("INT_SHR", vm, offset);
    case CODE_INT_EQ:
        return byteArgInstruction("INT_EQ", vm, offset);
    case CODE_INT_LESS:
        return byteArgInstruction("INT_LESS", vm, offset);
    case CODE_INT_GREATER:
        return byteArgInstruction("INT_GREATER", vm, offset);
    case CODE_INT_SIGN:
        return byteArgInstruction("INT_SIGN", vm, offset);
    case CODE_SINGLE_NEG:
        return simpleInstruction("SINGLE_NEG", offset);
    case CODE_SINGLE_ADD:
        return simpleInstruction("SINGLE_ADD", offset);
    case CODE_SINGLE_SUB:
        return simpleInstruction("SINGLE_SUB", offset);
    case CODE_SINGLE_MUL:
        return simpleInstruction("SINGLE_MUL", offset);
    case CODE_SINGLE_DIV:
        return simpleInstruction("SINGLE_DIV", offset);
    case CODE_SINGLE_EQ:
        return simpleInstruction("SINGLE_EQ", offset);
    case CODE_SINGLE_LESS:
        return simpleInstruction("SINGLE_LESS", offset);
    case CODE_SINGLE_GREATER:
        return simpleInstruction("SINGLE_GREATER", offset);
    case CODE_SINGLE_SIGN:
        return simpleInstruction("SINGLE_SIGN", offset);
    case CODE_DOUBLE_NEG:
        return simpleInstruction("DOUBLE_NEG", offset);
    case CODE_DOUBLE_ADD:
        return simpleInstruction("DOUBLE_ADD", offset);
    case CODE_DOUBLE_SUB:
        return simpleInstruction("DOUBLE_SUB", offset);
    case CODE_DOUBLE_MUL:
        return simpleInstruction("DOUBLE_MUL", offset);
    case CODE_DOUBLE_DIV:
        return simpleInstruction("DOUBLE_DIV", offset);
    case CODE_DOUBLE_EQ:
        return simpleInstruction("DOUBLE_EQ", offset);
    case CODE_DOUBLE_LESS:
        return simpleInstruction("DOUBLE_LESS", offset);
    case CODE_DOUBLE_GREATER:
        return simpleInstruction("DOUBLE_GREATER", offset);
    case CODE_DOUBLE_SIGN:
        return simpleInstruction("DOUBLE_SIGN", offset);
    case CODE_VALUE_CONV: {
        uint8_t* code = vm->code.data;
        offset += 1;

        uint8_t from = code[offset];
        offset += 1;
        uint8_t to = code[offset];
        offset += 1;
        printf("%-16s %d -> %d", "VALUE_CONV", from, to);
        return offset;
    }
    case CODE_STORE:
        return byteArgInstruction("STORE", vm, offset);
    case CODE_FIND: {
        uint8_t* code = vm->code.data;
        offset += 1;

        uint16_t frameIdx = getShort(code, offset);
        offset += 2;
        uint16_t varIdx = getShort(code, offset);
        offset += 2;
        printf("%-16s %-5d %-5d\n", "FIND", frameIdx, varIdx);
        return offset;
    }
    case CODE_FORGET:
        return simpleInstruction("FORGET", offset);
    case CODE_CALL_FOREIGN:
        return shortArgInstruction("CALL_FOREIGN", vm, offset);
    case CODE_CALL:
        return callInstruction("CALL", vm, offset);
    case CODE_TAILCALL:
        return callInstruction("TAILCALL", vm, offset);
    case CODE_OFFSET:
        return intArgInstruction("OFFSET", vm, offset);
    case CODE_RETURN:
        return simpleInstruction("RETURN", offset);
    case CODE_JUMP_TRUE:
        return intArgInstruction("JUMP_TRUE", vm, offset);
    case CODE_JUMP_FALSE:
        return intArgInstruction("JUMP_FALSE", vm, offset);
    case CODE_OFFSET_TRUE:
        return intArgInstruction("OFFSET_TRUE", vm, offset);
    case CODE_OFFSET_FALSE:
        return intArgInstruction("OFFSET_FALSE", vm, offset);
    case CODE_CLOSURE:
        return closureInstruction("CLOSURE", vm, offset);
    case CODE_RECURSIVE:
        return closureInstruction("RECURSIVE", vm, offset);
    case CODE_MUTUAL:
        return intArgInstruction("MUTUAL", vm, offset);
    case CODE_CLOSURE_ONCE:
        return simpleInstruction("CLOSURE_ONCE", offset);
    case CODE_CLOSURE_ONCE_TAIL:
        return simpleInstruction("CLOSURE_ONCE_TAIL", offset);
    case CODE_CLOSURE_MANY:
        return simpleInstruction("CLOSURE_MANY", offset);
    case CODE_HANDLE: {
        uint8_t* code = vm->code.data;
        offset += 1;

        int16_t after = getShort(code, offset);
        offset += 2;
        int handleId = getInt(code, offset);
        offset += 4;
        uint8_t params = code[offset];
        offset += 1;
        uint8_t handlers = code[offset];
        offset += 1;
        printf("%-16s a(%d) id(%d) p(%d) h(%d)\n", "HANDLE", after, handleId, params, handlers);
        return offset;
    }
    case CODE_INJECT:
        return intArgInstruction("INJECT", vm, offset);
    case CODE_EJECT:
        return intArgInstruction("EJECT", vm, offset);
    case CODE_COMPLETE:
        return simpleInstruction("COMPLETE", offset);
    case CODE_ESCAPE:
        return actionInstruction("ESCAPE", vm, offset);
    case CODE_CALL_CONTINUATION:
        return simpleInstruction("CALL_CONTINUATION", offset);
    case CODE_TAILCALL_CONTINUATION:
        return simpleInstruction("TAILCALL_CONTINUATION", offset);
    case CODE_THREAD_SPAWN:
        return intArgInstruction("THREAD_SPAWN", vm, offset);
    case CODE_THREAD_SPAWN_WITH:
        return twoIntArgInstruction("THREAD_SPAWN_WITH", vm, offset);
    case CODE_THREAD_SPAWN_COPY:
        return simpleInstruction("THREAD_SPAWN_COPY", offset);
    case CODE_THREAD_CURRENT:
        return simpleInstruction("THREAD_CURRENT", offset);
    case CODE_THREAD_SLEEP:
        return simpleInstruction("THREAD_SLEEP", offset);
    case CODE_THREAD_YIELD:
        return simpleInstruction("THREAD_YIELD", offset);
    case CODE_THREAD_JOIN:
        return simpleInstruction("THREAD_JOIN", offset);
    case CODE_THREAD_EQUAL:
        return simpleInstruction("THREAD_EQUAL", offset);
    case CODE_ZAP:
        return simpleInstruction("ZAP", offset);
    case CODE_DUP:
        return simpleInstruction("DUP", offset);
    case CODE_SWAP:
        return simpleInstruction("SWAP", offset);
    case CODE_SHUFFLE: {
        uint8_t* code = vm->code.data;
        offset += 1;

        uint8_t pop = code[offset];
        offset += 1;
        uint8_t push = code[offset];
        offset += 1;
        printf("%-16s %-3d -> ", "SHUFFLE", pop);
        for (int i = 0; i < push; i++) {
            printf("%d ", code[offset]);
            offset += 1;
        }
        printf("\n");

        return offset;
    }
    case CODE_NEWREF:
        return simpleInstruction("NEWREF", offset);
    case CODE_GETREF:
        return simpleInstruction("GETREF", offset);
    case CODE_PUTREF:
        return simpleInstruction("PUTREF", offset);
    case CODE_CONSTRUCT: {
        uint8_t* code = vm->code.data;
        offset += 1;

        int structId = getInt(code, offset);
        offset += 4;
        uint8_t count = code[offset];
        offset += 1;
        printf("%-16s %d - %d\n", "CONSTRUCT", structId, count);
        return offset;
    }
    case CODE_DESTRUCT:
        return simpleInstruction("DESTRUCT", offset);
    case CODE_IS_STRUCT:
        return intArgInstruction("IS_STRUCT", vm, offset);
    case CODE_JUMP_STRUCT:
        return twoIntArgInstruction("JUMP_STRUCT", vm, offset);
    case CODE_OFFSET_STRUCT:
        return twoIntArgInstruction("OFFSET_STRUCT", vm, offset);
    case CODE_RECORD_NIL:
        return simpleInstruction("RECORD_NIL", offset);
    case CODE_RECORD_EXTEND:
        return intArgInstruction("RECORD_EXTEND", vm, offset);
    case CODE_RECORD_SELECT:
        return intArgInstruction("RECORD_SELECT", vm, offset);
    case CODE_RECORD_RESTRICT:
        return intArgInstruction("RECORD_RESTRICT", vm, offset);
    case CODE_RECORD_UPDATE:
        return intArgInstruction("RECORD_UPDATE", vm, offset);
    case CODE_VARIANT:
        return intArgInstruction("VARIANT", vm, offset);
    case CODE_EMBED:
        return intArgInstruction("EMBED", vm, offset);
    case CODE_IS_CASE:
        return intArgInstruction("IS_CASE", vm, offset);
    case CODE_JUMP_CASE:
        return twoIntArgInstruction("JUMP_CASE", vm, offset);
    case CODE_OFFSET_CASE:
        return twoIntArgInstruction("OFFSET_CASE", vm, offset);
    case CODE_LIST_NIL:
        return simpleInstruction("LIST_NIL", offset);
    case CODE_LIST_CONS:
        return simpleInstruction("LIST_CONS", offset);
    case CODE_LIST_HEAD:
        return simpleInstruction("LIST_HEAD", offset);
    case CODE_LIST_TAIL:
        return simpleInstruction("LIST_TAIL", offset);
    case CODE_LIST_IS_EMPTY:
        return simpleInstruction("LIST_IS_EMPTY", offset);
    case CODE_LIST_APPEND:
        return simpleInstruction("LIST_APPEND", offset);
    case CODE_ARRAY_NIL:
        return simpleInstruction("ARRAY_NIL", offset);
    case CODE_ARRAY_FILL:
        return simpleInstruction("ARRAY_FILL", offset);
    case CODE_ARRAY_SNOC:
        return simpleInstruction("ARRAY_SNOC", offset);
    case CODE_ARRAY_GET_AT:
        return simpleInstruction("ARRAY_GET_AT", offset);
    case CODE_ARRAY_SET_AT:
        return simpleInstruction("ARRAY_SET_AT", offset);
    case CODE_ARRAY_LENGTH:
        return simpleInstruction("ARRAY_LENGTH", offset);
    case CODE_ARRAY_COPY:
        return simpleInstruction("ARRAY_COPY", offset);
    case CODE_ARRAY_CONCAT:
        return simpleInstruction("ARRAY_CONCAT", offset);
    case CODE_ARRAY_SLICE:
        return simpleInstruction("ARRAY_SLICE", offset);
    case CODE_SUBSLICE:
        return simpleInstruction("SUBSLICE", offset);
    case CODE_SLICE_GET_AT:
        return simpleInstruction("SLICE_GET_AT", offset);
    case CODE_SLICE_SET_AT:
        return simpleInstruction("SLICE_SET_AT", offset);
    case CODE_SLICE_LENGTH:
        return simpleInstruction("SLICE_LENGTH", offset);
    case CODE_SLICE_COPY:
        return simpleInstruction("SLICE_COPY", offset);
    case CODE_BYTE_ARRAY_NIL:
        return simpleInstruction("BYTE_ARRAY_NIL", offset);
    case CODE_BYTE_ARRAY_FILL:
        return simpleInstruction("BYTE_ARRAY_FILL", offset);
    case CODE_BYTE_ARRAY_SNOC:
        return simpleInstruction("BYTE_ARRAY_SNOC", offset);
    case CODE_BYTE_ARRAY_GET_AT:
        return simpleInstruction("BYTE_ARRAY_GET_AT", offset);
    case CODE_BYTE_ARRAY_SET_AT:
        return simpleInstruction("BYTE_ARRAY_SET_AT", offset);
    case CODE_BYTE_ARRAY_LENGTH:
        return simpleInstruction("BYTE_ARRAY_LENGTH", offset);
    case CODE_BYTE_ARRAY_COPY:
        return simpleInstruction("BYTE_ARRAY_COPY", offset);
    case CODE_BYTE_ARRAY_CONCAT:
        return simpleInstruction("BYTE_ARRAY_CONCAT", offset);
    case CODE_BYTE_ARRAY_SLICE:
        return simpleInstruction("BYTE_ARRAY_SLICE", offset);
    case CODE_BYTE_SUBSLICE:
        return simpleInstruction("BYTE_SUBSLICE", offset);
    case CODE_BYTE_SLICE_GET_AT:
        return simpleInstruction("BYTE_SLICE_GET_AT", offset);
    case CODE_BYTE_SLICE_SET_AT:
        return simpleInstruction("BYTE_SLICE_SET_AT", offset);
    case CODE_BYTE_SLICE_LENGTH:
        return simpleInstruction("BYTE_SLICE_LENGTH", offset);
    case CODE_BYTE_SLICE_COPY:
        return simpleInstruction("BYTE_SLICE_COPY", offset);
    case CODE_STRING_CONCAT:
        return simpleInstruction("STRING_CONCAT", offset);
    case CODE_PRINT:
        return simpleInstruction("PRINT", offset);
    default:
        printf("Unknown opcode %d\n", instruction);
        return offset + 1;
    }
}

void printFiberValueStack(MochiVM* vm, ObjFiber* fiber) {
    ASSERT(fiber->valueStack <= fiber->valueStackTop, "Value stack underflow.");
    printf("VALUES:    ");
    if (fiber->valueStack >= fiber->valueStackTop) {
        printf("<empty>");
    }
    for (Value* slot = fiber->valueStack; slot < fiber->valueStackTop; slot++) {
        printf("[ ");
        printValue(vm, *slot);
        printf(" ]");
    }
    printf("\n");
}

void printFiberFrameStack(MochiVM* vm, ObjFiber* fiber) {
    ASSERT(fiber->frameStack <= fiber->frameStackTop, "Frame stack underflow.");
    printf("FRAMES:    ");
    if (fiber->frameStack >= fiber->frameStackTop) {
        printf("<empty>");
    }
    for (ObjVarFrame** frame = fiber->frameStack; frame < fiber->frameStackTop; frame++) {
        printf("[ ");
        printObject(vm, OBJ_VAL(*frame));
        printf(" ]");
    }
    printf("\n");
}

void printFiberRootStack(MochiVM* vm, ObjFiber* fiber) {
    printf("ROOTS:     ");
    if (fiber->rootStack >= fiber->rootStackTop) {
        printf("<empty>");
    }
    for (Obj** root = fiber->rootStack; root < fiber->rootStackTop; root++) {
        printf("[ ");
        printObject(vm, OBJ_VAL(*root));
        printf(" ]");
    }
    printf("\n");
}