package runtime

import (
	"encoding/binary"
	"io"
)

type HeapKey = uint

type CodePointer = uint

type NativeFn = func(*Machine, *Fiber)

type Machine struct {
	rdr io.Reader

	code      []byte
	lines     []uint
	constants []Value

	labels       []string
	labelIndices []uint

	heap        map[HeapKey]Value
	nextHeapKey HeapKey

	nativeFns []NativeFn
}

// Generic function to create a call frame from a closure based on some data
// known about it. Can supply a var frame that will be spliced between the
// parameters and the captured values, but if this isn't needed, supply `nil`
// for it. Modifies the fiber stack, and expects the parameters to be in
// correct order at the top of the stack.
func (m *Machine) callClosureFrame(fiber *Fiber, closure Closure, vars *VariableFrame, cont *Continuation, after uint) CallFrame {
	varCount := closure.paramCount + uint(len(closure.captured))
	if vars != nil {
		varCount += uint(len(vars.slots))
	}
	if cont != nil {
		varCount += 1
	}
	frameSlots := make([]Value, varCount)

	offset := 0
	if cont != nil {
		frameSlots[offset] = *cont
		offset += 1
	}

	for i := 0; i < int(closure.paramCount); i++ {
		frameSlots[offset] = fiber.PopOneValue()
	}

	if vars != nil {
		copy(frameSlots[offset:offset+len(vars.slots)], vars.slots)
		offset += len(vars.slots)
	}

	copy(frameSlots[offset:offset+len(closure.captured)], closure.captured)
	return CallFrame{VariableFrame{frameSlots}, after}
}

func (m *Machine) Run(fiber *Fiber) int32 {
	for {
		switch m.ReadInstruction(fiber) {
		case NOP:
			// do nothing
		case BREAKPOINT:
			panic("BREAKPOINT is not yet implemented.")
		case ABORT:
			result := fiber.PopOneValue().(int32)
			return result
		case CONSTANT:
			panic("CONSTANT is not yet implemented.")

		// BOOLEAN INSTRUCTIONS
		case TRUE:
			fiber.PushValue(true)
		case FALSE:
			fiber.PushValue(false)
		case BOOL_NOT:
			b := fiber.PopOneValue().(bool)
			fiber.PushValue(!b)
		case BOOL_AND:
			l, r := fiber.PopTwoValues()
			fiber.PushValue(l.(bool) && r.(bool))
		case BOOL_OR:
			l, r := fiber.PopTwoValues()
			fiber.PushValue(l.(bool) || r.(bool))
		case BOOL_NEQ:
			l, r := fiber.PopTwoValues()
			fiber.PushValue(l.(bool) != r.(bool))
		case BOOL_EQ:
			l, r := fiber.PopTwoValues()
			fiber.PushValue(l.(bool) == r.(bool))

		// IMMEDIATE PUSH INSTRUCTIONS
		case I8:
			fiber.PushValue(m.ReadInt8(fiber))
		case U8:
			fiber.PushValue(m.ReadUInt8(fiber))
		case I16:
			fiber.PushValue(m.ReadInt16(fiber))
		case U16:
			fiber.PushValue(m.ReadUInt16(fiber))
		case I32:
			fiber.PushValue(m.ReadInt32(fiber))
		case U32:
			fiber.PushValue(m.ReadUInt32(fiber))
		case I64:
			fiber.PushValue(m.ReadInt64(fiber))
		case U64:
			fiber.PushValue(m.ReadUInt64(fiber))
		case SINGLE:
			fiber.PushValue(m.ReadSingle(fiber))
		case DOUBLE:
			fiber.PushValue(m.ReadDouble(fiber))

		// NUMERIC OPERATIONS
		case NUM_NEG:
			m.UnaryNumeric(fiber, Negate)
		case NUM_INC:
			m.UnaryNumeric(fiber, Increment)
		case NUM_DEC:
			m.UnaryNumeric(fiber, Decrement)
		case NUM_ADD:
			m.BinaryNumeric(fiber, Add)
		case NUM_SUB:
			m.BinaryNumeric(fiber, Subtract)
		case NUM_MUL:
			m.BinaryNumeric(fiber, Multiply)
		case NUM_DIV_REM_T:
			m.BinaryNumericBinaryOut(fiber, DivRemT)
		case NUM_DIV_REM_F:
			m.BinaryNumericBinaryOut(fiber, DivRemF)
		case NUM_DIV_REM_E:
			m.BinaryNumericBinaryOut(fiber, DivRemE)
		case INT_OR:
			m.BinaryNumeric(fiber, BitwiseOr)
		case INT_AND:
			m.BinaryNumeric(fiber, BitwiseAnd)
		case INT_XOR:
			m.BinaryNumeric(fiber, BitwiseXor)
		case INT_COMP:
			m.UnaryNumeric(fiber, Complement)
		case INT_SHL:
			m.BinaryNumeric(fiber, ShiftLeft)
		case INT_SHR:
			m.BinaryNumeric(fiber, ShiftRight)
		case NUM_EQ:
			m.BinaryNumeric(fiber, Equal)
		case NUM_LT:
			m.BinaryNumeric(fiber, LessThan)
		case NUM_GT:
			m.BinaryNumeric(fiber, GreaterThan)
		case NUM_SIGN:
			m.UnaryNumeric(fiber, Sign)

		// PRIMITIVE VALUE CONVERSIONS
		case VALUE_CONV:
			panic("VALUE_CONV not yet implemented.")

		// VARIABLE FRAME OPERATIONS
		case STORE:
			valsLen := len(fiber.values)
			varCount := int(m.ReadUInt8(fiber))
			if valsLen < varCount {
				panic("STORE: Not enough values to store in frame")
			}
			frame := VariableFrame{make([]Value, varCount)}
			copy(frame.slots, fiber.values[valsLen-varCount:])
			fiber.PushFrame(frame)
		case FIND:
			frameIdx := m.ReadUInt16(fiber)
			slotIdx := m.ReadUInt16(fiber)
			frame := fiber.PeekFrameAt(uint(frameIdx))
			fiber.PushValue(frame.Slots()[slotIdx])
		case OVERWRITE:
			frameIdx := m.ReadUInt16(fiber)
			slotIdx := m.ReadUInt16(fiber)
			frame := fiber.PeekFrameAt(uint(frameIdx))
			frame.Slots()[slotIdx] = fiber.PopOneValue()
		case FORGET:
			fiber.PopFrame()

		case CALL_NATIVE:
			fnIndex := m.ReadUInt16(fiber)
			fn := m.nativeFns[fnIndex]
			fn(m, fiber)

		case CALL:
			fnStart := m.ReadUInt32(fiber)
			frame := CallFrame{VariableFrame{make([]Value, 0)}, fiber.instruction}
			fiber.PushFrame(frame)
			fiber.instruction = uint(fnStart)
		case TAILCALL:
			fiber.instruction = uint(m.ReadUInt32(fiber))
		case CALL_CLOSURE:
			closure := fiber.PopOneValue()

		}
	}
}

func (m *Machine) UnaryNumeric(fiber *Fiber, unary func(Instruction, Value) Value) {
	fiber.PushValue(unary(m.ReadInstruction(fiber), fiber.PopOneValue()))
}

func (m *Machine) BinaryNumeric(fiber *Fiber, binary func(Instruction, Value, Value) Value) {
	l, r := fiber.PopTwoValues()
	fiber.PushValue(binary(m.ReadInstruction(fiber), l, r))
}

func (m *Machine) BinaryNumericBinaryOut(fiber *Fiber, binary func(Instruction, Value, Value) (Value, Value)) {
	l, r := fiber.PopTwoValues()
	b, t := binary(m.ReadInstruction(fiber), l, r)
	fiber.PushValue(b)
	fiber.PushValue(t)
}

func (m *Machine) ReadInstruction(f *Fiber) Instruction {
	return m.ReadUInt8(f)
}

func (m *Machine) ReadInt8(f *Fiber) int8 {
	var result int8
	err := binary.Read(m.rdr, binary.BigEndian, &result)
	if err != nil {
		panic(err)
	}
	f.instruction += 1
	return result
}

func (m *Machine) ReadUInt8(f *Fiber) uint8 {
	result := m.code[f.instruction]
	f.instruction++
	return result
}

func (m *Machine) ReadInt16(f *Fiber) int16 {
	var result int16
	err := binary.Read(m.rdr, binary.BigEndian, &result)
	if err != nil {
		panic(err)
	}
	f.instruction += 2
	return result
}

func (m *Machine) ReadUInt16(f *Fiber) uint16 {
	var result uint16
	err := binary.Read(m.rdr, binary.BigEndian, &result)
	if err != nil {
		panic(err)
	}
	f.instruction += 2
	return result
}

func (m *Machine) ReadInt32(f *Fiber) int32 {
	var result int32
	err := binary.Read(m.rdr, binary.BigEndian, &result)
	if err != nil {
		panic(err)
	}
	f.instruction += 4
	return result
}

func (m *Machine) ReadUInt32(f *Fiber) uint32 {
	var result uint32
	err := binary.Read(m.rdr, binary.BigEndian, &result)
	if err != nil {
		panic(err)
	}
	f.instruction += 4
	return result
}

func (m *Machine) ReadInt64(f *Fiber) int64 {
	var result int64
	err := binary.Read(m.rdr, binary.BigEndian, &result)
	if err != nil {
		panic(err)
	}
	f.instruction += 8
	return result
}

func (m *Machine) ReadUInt64(f *Fiber) uint64 {
	var result uint64
	err := binary.Read(m.rdr, binary.BigEndian, &result)
	if err != nil {
		panic(err)
	}
	f.instruction += 8
	return result
}

func (m *Machine) ReadSingle(f *Fiber) float32 {
	var result float32
	err := binary.Read(m.rdr, binary.BigEndian, &result)
	if err != nil {
		panic(err)
	}
	f.instruction += 4
	return result
}

func (m *Machine) ReadDouble(f *Fiber) float64 {
	var result float64
	err := binary.Read(m.rdr, binary.BigEndian, &result)
	if err != nil {
		panic(err)
	}
	f.instruction += 8
	return result
}
