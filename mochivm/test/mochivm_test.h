
#define CONST_DOUBLE(arg)      mochiWriteDoubleConst(vm, (arg));
#define CONST_I32(arg)         mochiWriteI32Const(vm, (arg));
#define WRITE_INST(inst, line) mochiWriteCodeByte(vm, CODE_##inst, (line));
#define WRITE_BYTE(byte, line) mochiWriteCodeByte(vm, (byte), (line));
#define WRITE_LABEL(label)     mochiWriteLabel(vm, vm->code.count, label)

#define WRITE_SHORT(val, line) mochiWriteCodeU16(vm, val, line);
#define WRITE_INT(val, line)   mochiWriteCodeI32(vm, val, line);

#define WRITE_INT_INST(inst, arg, line)                                                                                \
    do {                                                                                                               \
        mochiWriteCodeByte(vm, CODE_##inst, (line));                                                                   \
        mochiWriteCodeI32(vm, arg, line);                                                                              \
    } while (false);

MochiVM* vm;

void vm_setup() {
    vm = mochiNewVM(NULL);
}

void vm_teardown() {
    mochiFreeVM(vm);
}