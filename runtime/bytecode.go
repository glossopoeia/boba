package runtime

import (
	"bytes"
	"encoding/binary"
	"fmt"
)

type Instruction = byte

const (
	NOP Instruction = iota
	BREAKPOINT
	ABORT

	PERM_QUERY
	PERM_REQUEST
	PERM_REQUEST_ALL
	PERM_REVOKE
	JUMP_PERMISSION
	OFFSET_PERMISSION

	TRUE
	FALSE
	BOOL_NOT
	BOOL_AND
	BOOL_OR
	BOOL_NEQ
	BOOL_EQ

	CONSTANT

	BOOL
	I8
	U8
	I16
	U16
	I32
	U32
	I64
	U64
	INATIVE
	UNATIVE
	SINGLE
	DOUBLE

	NUM_NEG
	NUM_INC
	NUM_DEC
	NUM_ADD
	NUM_SUB
	NUM_MUL
	NUM_DIV_REM_T
	NUM_DIV_REM_F
	NUM_DIV_REM_E
	INT_OR
	INT_AND
	INT_XOR
	INT_COMP
	INT_SHL
	INT_SHR
	NUM_EQ
	NUM_LT
	NUM_GT
	NUM_SIGN

	VALUE_CONV

	STORE
	FIND
	OVERWRITE
	FORGET

	CALL_NATIVE

	OFFSET
	CALL
	TAILCALL
	CALL_CLOSURE
	TAILCALL_CLOSURE
	RETURN

	JUMP_TRUE
	JUMP_FALSE
	OFFSET_TRUE
	OFFSET_FALSE

	CLOSURE
	RECURSIVE
	MUTUAL
	CLOSURE_ONCE
	CLOSURE_ONCE_TAIL
	CLOSURE_NEVER

	HANDLE
	INJECT
	EJECT
	COMPLETE
	ESCAPE
	CALL_CONTINUATION
	TAILCALL_CONTINUATION

	SWAP
	DUP
	ZAP
	SHUFFLE

	NEWREF
	GETREF
	PUTREF

	CONSTRUCT
	DESTRUCT
	IS_COMPOSITE
	JUMP_COMPOSITE
	OFFSET_COMPOSITE

	RECORD_NIL
	RECORD_EXTEND
	RECORD_SELECT
	RECORD_UPDATE

	VARIANT
	IS_CASE
	JUMP_CASE
	OFFSET_CASE

	ARRAY_NIL
	ARRAY_FILL
	ARRAY_SNOC
	ARRAY_GET_AT
	ARRAY_SET_AT
	ARRAY_LENGTH
	ARRAY_COPY
	ARRAY_CONCAT

	ARRAY_SLICE

	STRING_CONCAT
	PRINT
)

func (m *Machine) Disassemble() {
	for i := 0; i < len(m.code); {
		i = int(m.DisassembleInstruction(uint(i)))
	}
}

func (m *Machine) DisassembleInstruction(offset uint) uint {
	fmt.Printf("%04d ", offset)
	if offset > 0 && m.lines[offset] == m.lines[offset-1] {
		fmt.Printf("   | ")
	} else {
		fmt.Printf("%4d ", m.lines[offset])
	}

	instruction := m.code[offset]
	switch instruction {
	case NOP:
		return m.simpleInstruction("NOP", offset)
	case BREAKPOINT:
		return m.simpleInstruction("BREAKPOINT", offset)
	case ABORT:
		return m.simpleInstruction("ABORT", offset)
	case CONSTANT:
		constIdx, next := m.ReadUInt16(offset + 1)
		fmt.Printf("CONSTANT: %v\n", m.constants[constIdx])
		return next
	case TRUE:
		return m.simpleInstruction("TRUE", offset)
	case FALSE:
		return m.simpleInstruction("FALSE", offset)
	case BOOL_NOT:
		return m.simpleInstruction("BOOL_NOT", offset)
	case BOOL_AND:
		return m.simpleInstruction("BOOL_AND", offset)
	case BOOL_OR:
		return m.simpleInstruction("BOOL_OR", offset)
	case BOOL_NEQ:
		return m.simpleInstruction("BOOL_NEQ", offset)
	case BOOL_EQ:
		return m.simpleInstruction("BOOL_EQ", offset)
	case I8:
		arg, next := m.ReadInt8(offset + 1)
		fmt.Printf("I8: %d\n", arg)
		return next
	case U8:
		return m.byteArgInstruction("U8", offset)
	case I16:
		arg, next := m.ReadInt16(offset + 1)
		fmt.Printf("I16: %d\n", arg)
		return next
	case U16:
		arg, next := m.ReadUInt16(offset + 1)
		fmt.Printf("U16: %d\n", arg)
		return next
	case I32:
		arg, next := m.ReadInt32(offset + 1)
		fmt.Printf("I32: %d\n", arg)
		return next
	case U32:
		arg, next := m.ReadUInt32(offset + 1)
		fmt.Printf("U32: %d\n", arg)
		return next
	case I64:
		arg, next := m.ReadInt64(offset + 1)
		fmt.Printf("I64: %d\n", arg)
		return next
	case U64:
		arg, next := m.ReadUInt64(offset + 1)
		fmt.Printf("U64: %d\n", arg)
		return next
	case SINGLE:
		arg, next := m.ReadSingle(offset + 1)
		fmt.Printf("SINGLE: %f\n", arg)
		return next
	case DOUBLE:
		arg, next := m.ReadDouble(offset + 1)
		fmt.Printf("DOUBLE: %f\n", arg)
		return next
	case NUM_NEG:
		return m.numericInstruction("NUM_NEG", offset)
	case NUM_INC:
		return m.numericInstruction("NUM_INC", offset)
	case NUM_DEC:
		return m.numericInstruction("NUM_DEC", offset)
	case NUM_ADD:
		return m.numericInstruction("NUM_ADD", offset)
	case NUM_SUB:
		return m.numericInstruction("NUM_SUB", offset)
	case NUM_MUL:
		return m.numericInstruction("NUM_MUL", offset)
	case NUM_DIV_REM_T:
		return m.numericInstruction("NUM_DIV_REM_T", offset)
	case NUM_DIV_REM_F:
		return m.numericInstruction("NUM_DIV_REM_F", offset)
	case NUM_DIV_REM_E:
		return m.numericInstruction("NUM_DIV_REM_E", offset)
	case INT_OR:
		return m.numericInstruction("INT_OR", offset)
	case INT_AND:
		return m.numericInstruction("INT_AND", offset)
	case INT_XOR:
		return m.numericInstruction("INT_XOR", offset)
	case INT_COMP:
		return m.numericInstruction("INT_COMP", offset)
	case INT_SHL:
		return m.numericInstruction("INT_SHL", offset)
	case INT_SHR:
		return m.numericInstruction("INT_SHR", offset)
	case NUM_EQ:
		return m.numericInstruction("NUM_EQ", offset)
	case NUM_LT:
		return m.numericInstruction("NUM_LT", offset)
	case NUM_GT:
		return m.numericInstruction("NUM_GT", offset)
	case NUM_SIGN:
		return m.numericInstruction("NUM_SIGN", offset)
	case VALUE_CONV:
		from, aft1 := m.ReadUInt8(offset + 1)
		to, aft2 := m.ReadUInt8(aft1)
		fmt.Printf("VALUE_CONV: %s -> %s\n", numericType(from), numericType(to))
		return aft2
	case STORE:
		arg, next := m.ReadInt8(offset + 1)
		fmt.Printf("STORE: %d\n", arg)
		return next
	case FIND:
		frameIdx, aft1 := m.ReadUInt16(offset + 1)
		slotIdx, aft2 := m.ReadUInt16(aft1)
		fmt.Printf("FIND: %d, %d\n", frameIdx, slotIdx)
		return aft2
	case OVERWRITE:
		panic("Disassembly of OVERWRITE instruction not yet supported.")
	case FORGET:
		return m.simpleInstruction("FORGET", offset)
	case CALL_NATIVE:
		nativeIdx, aft := m.ReadUInt16(offset + 1)
		fmt.Printf("CALL_NATIVE: %s\n", m.nativeFnNames[nativeIdx])
		return aft
	case CALL:
		return m.jumpInstruction("CALL", offset)
	case TAILCALL:
		return m.jumpInstruction("TAILCALL", offset)
	case CALL_CLOSURE:
		return m.simpleInstruction("CALL_CLOSURE", offset)
	case TAILCALL_CLOSURE:
		return m.simpleInstruction("TAILCALL_CLOSURE", offset)
	case OFFSET:
		return m.offsetInstruction("OFFSET", offset)
	case RETURN:
		return m.simpleInstruction("RETURN", offset)
	case JUMP_TRUE:
		return m.jumpInstruction("JUMP_TRUE", offset)
	case JUMP_FALSE:
		return m.jumpInstruction("JUMP_FALSE", offset)
	case OFFSET_TRUE:
		return m.offsetInstruction("OFFSET_TRUE", offset)
	case OFFSET_FALSE:
		return m.offsetInstruction("OFFSET_FALSE", offset)
	case CLOSURE:
		return m.closureInstruction("CLOSURE", offset)
	case RECURSIVE:
		return m.closureInstruction("RECURSIVE", offset)
	case MUTUAL:
		return m.byteArgInstruction("MUTUAL", offset)
	case CLOSURE_ONCE:
		return m.simpleInstruction("CLOSURE_ONCE", offset)
	case CLOSURE_ONCE_TAIL:
		return m.simpleInstruction("CLOSURE_ONCE_TAIL", offset)
	case CLOSURE_NEVER:
		return m.simpleInstruction("CLOSURE_NEVER", offset)
	case HANDLE:
		after, aft1 := m.ReadUInt16(offset + 1)
		handleId, aft2 := m.ReadInt32(aft1)
		paramCount, aft3 := m.ReadUInt8(aft2)
		handlerCount, aft4 := m.ReadUInt8(aft3)
		fmt.Printf("HANDLE: a(%d) id(%d) p(%d) hs(%d)\n", after, handleId, paramCount, handlerCount)
		return aft4
	case INJECT:
		return m.intArgInstruction("INJECT", offset)
	case EJECT:
		return m.intArgInstruction("EJECT", offset)
	case COMPLETE:
		return m.simpleInstruction("COMPLETE", offset)
	case ESCAPE:
		handleId, aft1 := m.ReadInt32(offset + 1)
		handlerIdx, aft2 := m.ReadUInt8(aft1)
		fmt.Printf("ESCAPE: %d, %d\n", handleId, handlerIdx)
		return aft2
	case CALL_CONTINUATION:
		return m.simpleInstruction("CALL_CONTINUATION", offset)
	case TAILCALL_CONTINUATION:
		return m.simpleInstruction("TAILCALL_CONTINUATION", offset)
	case SWAP:
		return m.simpleInstruction("SWAP", offset)
	case DUP:
		return m.simpleInstruction("DUP", offset)
	case ZAP:
		return m.simpleInstruction("ZAP", offset)
	case SHUFFLE:
		panic("Disassembly of SHUFFLE instruction not yet supported.")
	case NEWREF:
		return m.simpleInstruction("NEWREF", offset)
	case GETREF:
		return m.simpleInstruction("GETREF", offset)
	case PUTREF:
		return m.simpleInstruction("PUTREF", offset)
	case CONSTRUCT:
		compositeId, aft1 := m.ReadInt32(offset + 1)
		paramCount, aft2 := m.ReadUInt8(aft1)
		fmt.Printf("CONSTRUCT: %d, %d\n", compositeId, paramCount)
		return aft2
	case DESTRUCT:
		return m.simpleInstruction("DESTRUCT", offset)
	case IS_COMPOSITE:
		return m.intArgInstruction("IS_COMPOSITE", offset)
	case JUMP_COMPOSITE:
		return m.jumpIdInstruction("JUMP_COMPOSITE", offset)
	case OFFSET_COMPOSITE:
		return m.offsetIdInstruction("OFFSET_COMPOSITE", offset)
	case RECORD_NIL:
		return m.simpleInstruction("RECORD_NIL", offset)
	case RECORD_EXTEND:
		return m.intArgInstruction("RECORD_EXTEND", offset)
	case RECORD_SELECT:
		return m.intArgInstruction("RECORD_SELECT", offset)
	case RECORD_UPDATE:
		return m.intArgInstruction("RECORD_UPDATE", offset)
	case VARIANT:
		return m.intArgInstruction("VARIANT", offset)
	case IS_CASE:
		return m.intArgInstruction("IS_CASE", offset)
	case JUMP_CASE:
		return m.jumpIdInstruction("JUMP_CASE", offset)
	case OFFSET_CASE:
		return m.offsetIdInstruction("OFFSET_CASE", offset)
	case STRING_CONCAT:
		return m.simpleInstruction("STRING_CONCAT", offset)
	case PRINT:
		return m.simpleInstruction("PRINT", offset)
	default:
		fmt.Printf("Unknown opcode: %d\n", instruction)
		return offset + 1
	}
}

func (m *Machine) simpleInstruction(instr string, offset uint) uint {
	fmt.Println(instr)
	return offset + 1
}

func numericType(typeId byte) string {
	switch typeId {
	case BOOL:
		return "BOOL"
	case I8:
		return "I8"
	case U8:
		return "U8"
	case I16:
		return "I16"
	case U16:
		return "U16"
	case I32:
		return "I32"
	case U32:
		return "U32"
	case I64:
		return "I64"
	case U64:
		return "U64"
	case INATIVE:
		return "INATIVE"
	case UNATIVE:
		return "UNATIVE"
	case SINGLE:
		return "SINGLE"
	case DOUBLE:
		return "DOUBLE"
	default:
		return "UNKNOWN"
	}
}

func (m *Machine) numericInstruction(instr string, offset uint) uint {
	fmt.Printf("%-16s %s\n", instr, numericType(m.code[offset+1]))
	return offset + 2
}

func (m *Machine) jumpInstruction(instr string, offset uint) uint {
	fnStart, aft := m.ReadUInt32(offset + 1)
	if val, hasLabel := m.labels[uint(fnStart)]; hasLabel {
		fmt.Printf("%s: %s\n", instr, val)
	} else {
		fmt.Printf("%s: %d\n", instr, fnStart)
	}
	return aft
}

func (m *Machine) jumpIdInstruction(instr string, offset uint) uint {
	id, idAft := m.ReadInt32(offset + 1)
	fnStart, aft := m.ReadUInt32(idAft)
	if val, hasLabel := m.labels[uint(fnStart)]; hasLabel {
		fmt.Printf("%s %d: %s\n", instr, id, val)
	} else {
		fmt.Printf("%s %d: %d\n", instr, id, fnStart)
	}
	return aft
}

func (m *Machine) offsetInstruction(instr string, offset uint) uint {
	fnStart, aft := m.ReadInt32(offset + 1)
	// TODO: int conversion here is probably bad
	if val, hasLabel := m.labels[uint(int(offset)+int(fnStart))]; hasLabel {
		fmt.Printf("%s: %s\n", instr, val)
	} else {
		fmt.Printf("%s: %d\n", instr, fnStart)
	}
	return aft
}

func (m *Machine) offsetIdInstruction(instr string, offset uint) uint {
	id, idAft := m.ReadInt32(offset + 1)
	fnStart, aft := m.ReadInt32(idAft)
	// TODO: int conversion here is probably bad
	if val, hasLabel := m.labels[uint(int(offset)+int(fnStart))]; hasLabel {
		fmt.Printf("%s %d: %s\n", instr, id, val)
	} else {
		fmt.Printf("%s %d: %d\n", instr, id, fnStart)
	}
	return aft
}

func (m *Machine) closureInstruction(instr string, offset uint) uint {
	fnStart, aft1 := m.ReadUInt32(offset + 1)
	paramCount, aft2 := m.ReadUInt8(aft1)
	closedCount, closedOffset := m.ReadUInt16(aft2)
	if val, hasLabel := m.labels[uint(fnStart)]; hasLabel {
		fmt.Printf("%s: %s, %d - ", instr, val, paramCount)
	} else {
		fmt.Printf("%s: %d, %d - ", instr, fnStart, paramCount)
	}
	for i := 0; i < int(closedCount); i++ {
		frameInd, aft4 := m.ReadUInt16(closedOffset)
		slotInd, aft5 := m.ReadUInt16(aft4)
		fmt.Printf("(%d, %d)", frameInd, slotInd)
		closedOffset = aft5
	}
	fmt.Println()
	return closedOffset
}

func (m *Machine) byteArgInstruction(instr string, offset uint) uint {
	val, aft := m.ReadUInt8(offset + 1)
	fmt.Printf("%s: %d\n", instr, val)
	return aft
}

func (m *Machine) intArgInstruction(instr string, offset uint) uint {
	val, aft := m.ReadInt32(offset + 1)
	fmt.Printf("%s: %d\n", instr, val)
	return aft
}

func (f *Fiber) ReadInstruction(m *Machine) Instruction {
	return f.ReadUInt8(m)
}

func (m *Machine) ReadInt8(offset uint) (int8, uint) {
	return int8(m.code[offset]), offset + 1
}

func (f *Fiber) ReadInt8(m *Machine) int8 {
	result, next := m.ReadInt8(f.instruction)
	f.instruction = next
	return result
}

func (m *Machine) ReadUInt8(offset uint) (uint8, uint) {
	result := m.code[offset]
	return result, offset + 1
}

func (f *Fiber) ReadUInt8(m *Machine) uint8 {
	result, next := m.ReadUInt8(f.instruction)
	f.instruction = next
	return result
}

func (m *Machine) ReadInt16(offset uint) (int16, uint) {
	result := (int16(m.code[offset]) << 8) | int16(m.code[offset+1])
	return result, offset + 2
}

func (f *Fiber) ReadInt16(m *Machine) int16 {
	result, next := m.ReadInt16(f.instruction)
	f.instruction = next
	return result
}

func (m *Machine) ReadUInt16(offset uint) (uint16, uint) {
	result := (uint16(m.code[offset]) << 8) | uint16(m.code[offset+1])
	return result, offset + 2
}

func (f *Fiber) ReadUInt16(m *Machine) uint16 {
	result, next := m.ReadUInt16(f.instruction)
	f.instruction = next
	return result
}

func (m *Machine) ReadInt32(offset uint) (int32, uint) {
	result := (int32(m.code[offset]) << 24) | (int32(m.code[offset+1]) << 16) | (int32(m.code[offset+2]) << 8) | int32(m.code[offset+3])
	return result, offset + 4
}

func (f *Fiber) ReadInt32(m *Machine) int32 {
	result, next := m.ReadInt32(f.instruction)
	f.instruction = next
	return result
}

func (m *Machine) ReadUInt32(offset uint) (uint32, uint) {
	result := (uint32(m.code[offset]) << 24) | (uint32(m.code[offset+1]) << 16) | (uint32(m.code[offset+2]) << 8) | uint32(m.code[offset+3])
	return result, offset + 4
}

func (f *Fiber) ReadUInt32(m *Machine) uint32 {
	result, next := m.ReadUInt32(f.instruction)
	f.instruction = next
	return result
}

func (m *Machine) ReadInt64(offset uint) (int64, uint) {
	result := (int64(m.code[offset]) << 56) |
		(int64(m.code[offset+1]) << 48) |
		(int64(m.code[offset+2]) << 40) |
		(int64(m.code[offset+3]) << 32) |
		(int64(m.code[offset+4]) << 24) |
		(int64(m.code[offset+5]) << 16) |
		(int64(m.code[offset+6]) << 8) |
		int64(m.code[offset+7])
	return result, offset + 8
}

func (f *Fiber) ReadInt64(m *Machine) int64 {
	result, next := m.ReadInt64(f.instruction)
	f.instruction = next
	return result
}

func (m *Machine) ReadUInt64(offset uint) (uint64, uint) {
	result := (uint64(m.code[offset]) << 56) |
		(uint64(m.code[offset+1]) << 48) |
		(uint64(m.code[offset+2]) << 40) |
		(uint64(m.code[offset+3]) << 32) |
		(uint64(m.code[offset+4]) << 24) |
		(uint64(m.code[offset+5]) << 16) |
		(uint64(m.code[offset+6]) << 8) |
		uint64(m.code[offset+7])
	return result, offset + 8
}

func (f *Fiber) ReadUInt64(m *Machine) uint64 {
	result, next := m.ReadUInt64(f.instruction)
	f.instruction = next
	return result
}

func (m *Machine) ReadSingle(offset uint) (float32, uint) {
	var result float32
	rdr := bytes.NewReader(m.code[offset:])
	err := binary.Read(rdr, binary.BigEndian, &result)
	if err != nil {
		panic(err)
	}
	return result, offset + 4
}

func (f *Fiber) ReadSingle(m *Machine) float32 {
	result, next := m.ReadSingle(f.instruction)
	f.instruction = next
	return result
}

func (m *Machine) ReadDouble(offset uint) (float64, uint) {
	var result float64
	rdr := bytes.NewReader(m.code[offset:])
	err := binary.Read(rdr, binary.BigEndian, &result)
	if err != nil {
		panic(err)
	}
	return result, offset + 8
}

func (f *Fiber) ReadDouble(m *Machine) float64 {
	result, next := m.ReadDouble(f.instruction)
	f.instruction = next
	return result
}

func (m *Machine) WriteI8(val int8, line uint) {
	m.code = append(m.code, byte(val))
	m.lines = append(m.lines, line)
}

func (m *Machine) WriteU8(val uint8, line uint) {
	m.code = append(m.code, byte(val))
	m.lines = append(m.lines, line)
}

func (m *Machine) WriteI16(val int16, line uint) {
	m.WriteU8(byte(val>>8), line)
	m.WriteU8(byte(val), line)
}

func (m *Machine) WriteU16(val uint16, line uint) {
	m.WriteU8(byte(val>>8), line)
	m.WriteU8(byte(val), line)
}

func (m *Machine) WriteI32(val int32, line uint) {
	m.WriteU8(byte(val>>24), line)
	m.WriteU8(byte(val>>16), line)
	m.WriteU8(byte(val>>8), line)
	m.WriteU8(byte(val), line)
}

func (m *Machine) WriteU32(val uint32, line uint) {
	m.WriteU8(byte(val>>24), line)
	m.WriteU8(byte(val>>16), line)
	m.WriteU8(byte(val>>8), line)
	m.WriteU8(byte(val), line)
}

func (m *Machine) WriteI64(val int64, line uint) {
	m.WriteU8(byte(val>>56), line)
	m.WriteU8(byte(val>>48), line)
	m.WriteU8(byte(val>>40), line)
	m.WriteU8(byte(val>>32), line)
	m.WriteU8(byte(val>>24), line)
	m.WriteU8(byte(val>>16), line)
	m.WriteU8(byte(val>>8), line)
	m.WriteU8(byte(val), line)
}

func (m *Machine) WriteU64(val uint64, line uint) {
	m.WriteU8(byte(val>>56), line)
	m.WriteU8(byte(val>>48), line)
	m.WriteU8(byte(val>>40), line)
	m.WriteU8(byte(val>>32), line)
	m.WriteU8(byte(val>>24), line)
	m.WriteU8(byte(val>>16), line)
	m.WriteU8(byte(val>>8), line)
	m.WriteU8(byte(val), line)
}

func (m *Machine) WriteSingle(val float32, line uint) {
	m.lines = append(m.lines, line, line, line, line)
	buf := new(bytes.Buffer)
	binary.Write(buf, binary.BigEndian, val)
	m.code = append(m.code, buf.Bytes()...)
}

func (m *Machine) WriteDouble(val float64, line uint) {
	m.lines = append(m.lines, line, line, line, line, line, line, line, line)
	buf := new(bytes.Buffer)
	binary.Write(buf, binary.BigEndian, val)
	m.code = append(m.code, buf.Bytes()...)
}
