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

func (m *Machine) restoreSaved(fiber *Fiber, frame HandleFrame, cont Continuation, after CodePointer) {
	// we basically copy the handle frame, but update the arguments passed along through the
	// handling context and forget the 'return location'
	updatedVars := VariableFrame{make([]Value, len(frame.slots))}
	updatedCall := CallFrame{updatedVars, after}
	updated := HandleFrame{updatedCall, frame.handleId, frame.nesting, frame.afterClosure, frame.handlers}

	// take any handle parameters off the stack
	for i := 0; i < len(frame.slots); i++ {
		updated.slots[i] = fiber.PopOneValue()
	}

	// captured stack values go under any remaining stack values
	fiber.values = append(cont.savedValues, fiber.values...)
	// saved frames just go on top of the existing frames
	fiber.PushFrame(updated)
	fiber.frames = append(fiber.frames, cont.savedFrames[1:]...)
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

		// FUNCTION AND CLOSURE CALL RELATED
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
			closure := fiber.PopOneValue().(Closure)
			frame := m.callClosureFrame(fiber, closure, nil, nil, fiber.instruction)
			fiber.PushFrame(frame)
			fiber.instruction = closure.codeStart
		case TAILCALL_CLOSURE:
			closure := fiber.PopOneValue().(Closure)
			frame := m.callClosureFrame(fiber, closure, nil, nil, fiber.PeekFrameAt(1).(CallFrame).afterLocation)
			fiber.PopFrame()
			fiber.PushFrame(frame)
			fiber.instruction = closure.codeStart
		case OFFSET:
			offset := m.ReadInt32(fiber)
			// TODO: this int() conversion is a bit bad
			fiber.instruction = uint(int32(fiber.instruction) + offset)
		case RETURN:
			frame := fiber.PopFrame().(CallFrame)
			fiber.instruction = frame.afterLocation

		// CONDITIONAL JUMPS
		case JUMP_TRUE:
			jump := m.ReadUInt32(fiber)
			if fiber.PopOneValue().(bool) {
				fiber.instruction = uint(jump)
			}
		case JUMP_FALSE:
			jump := m.ReadUInt32(fiber)
			if !fiber.PopOneValue().(bool) {
				fiber.instruction = uint(jump)
			}
		case OFFSET_TRUE:
			offset := m.ReadInt32(fiber)
			if fiber.PopOneValue().(bool) {
				// TODO: this int() conversion is a bit bad
				fiber.instruction = uint(int(offset) + int(fiber.instruction))
			}
		case OFFSET_FALSE:
			offset := m.ReadInt32(fiber)
			if !fiber.PopOneValue().(bool) {
				// TODO: this int() conversion is a bit bad
				fiber.instruction = uint(int(offset) + int(fiber.instruction))
			}

		// CLOSURE BUILDING
		case CLOSURE:
			codeStart := m.ReadUInt32(fiber)
			paramCount := m.ReadUInt8(fiber)
			closedCount := m.ReadUInt16(fiber)

			closure := Closure{CodePointer(codeStart), uint(paramCount), ResumeMany, make([]Value, closedCount)}
			for i := 0; i < int(closedCount); i++ {
				frameInd := m.ReadUInt16(fiber)
				slotInd := m.ReadUInt16(fiber)
				frame := fiber.frames[len(fiber.frames)-1-int(frameInd)]
				closure.captured[i] = frame.Slots()[slotInd]
			}
			fiber.PushValue(closure)
		case RECURSIVE:
			codeStart := m.ReadUInt32(fiber)
			paramCount := m.ReadUInt8(fiber)
			closedCount := m.ReadUInt16(fiber)

			closure := Closure{CodePointer(codeStart), uint(paramCount), ResumeMany, make([]Value, closedCount+1)}
			closure.captured[0] = closure
			for i := 0; i < int(closedCount); i++ {
				frameInd := m.ReadUInt16(fiber)
				slotInd := m.ReadUInt16(fiber)
				frame := fiber.frames[len(fiber.frames)-1-int(frameInd)]
				closure.captured[i+1] = frame.Slots()[slotInd]
			}
			fiber.PushValue(closure)
		case MUTUAL:
			mutualCount := int(m.ReadUInt8(fiber))
			// for each soon-to-be mutually referenced closure,
			// make a new closure with room for references to
			// the other closures and itself
			for i := 0; i < mutualCount; i++ {
				oldCInd := len(fiber.values) - 1 - i
				oldC := fiber.values[oldCInd].(Closure)
				newC := Closure{oldC.codeStart, oldC.paramCount, oldC.resumeLimit, make([]Value, len(oldC.captured)+mutualCount)}
				copy(newC.captured[mutualCount:len(newC.captured)], oldC.captured)
				fiber.values[oldCInd] = newC
			}
			// finally, make the closures all reference each other in the same order
			for i := 0; i < mutualCount; i++ {
				recC := fiber.values[len(fiber.values)-1-i].(Closure)
				copy(fiber.values[len(fiber.values)-mutualCount:len(fiber.values)], recC.captured[:mutualCount-1])
				fiber.values[len(fiber.values)-1-i] = recC
			}
		case CLOSURE_ONCE:
			closure := fiber.PopOneValue().(Closure)
			closure.resumeLimit = ResumeOnce
			fiber.PushValue(closure)
		case CLOSURE_ONCE_TAIL:
			closure := fiber.PopOneValue().(Closure)
			closure.resumeLimit = ResumeOnceTail
			fiber.PushValue(closure)
		case CLOSURE_NEVER:
			closure := fiber.PopOneValue().(Closure)
			closure.resumeLimit = ResumeNever
			fiber.PushValue(closure)

		// HANDLERS
		case HANDLE:
			after := int(m.ReadInt16(fiber))
			handleId := int(m.ReadInt32(fiber))
			paramCount := uint(m.ReadUInt8(fiber))
			handlerCount := uint(m.ReadUInt8(fiber))

			handlers := make([]Closure, handlerCount)
			for i := uint(0); i < handlerCount; i++ {
				handlers[i] = fiber.PopOneValue().(Closure)
			}
			afterClosure := fiber.PopOneValue().(Closure)

			params := make([]Value, paramCount)
			for i := uint(0); i < paramCount; i++ {
				params[i] = fiber.PopOneValue()
			}

			frame := HandleFrame{
				CallFrame{
					VariableFrame{
						params,
					},
					// TODO: this int() conversion is a bit bad
					uint(int(fiber.instruction) + after),
				},
				int(handleId),
				0,
				afterClosure,
				handlers,
			}
			fiber.PushFrame(frame)
		case INJECT:
			handleId := int(m.ReadInt32(fiber))
			for i := len(fiber.frames) - 1; i >= 0; i-- {
				frame := fiber.frames[i]
				switch frame.(type) {
				case HandleFrame:
					handle := frame.(HandleFrame)
					if handle.handleId == handleId {
						handle.nesting += 1
						if handle.nesting == 1 {
							break
						}
					}
					fiber.frames[i] = handle
				default:
					continue
				}
			}
		case EJECT:
			handleId := int(m.ReadInt32(fiber))
			for i := len(fiber.frames) - 1; i >= 0; i-- {
				frame := fiber.frames[i]
				switch frame.(type) {
				case HandleFrame:
					handle := frame.(HandleFrame)
					if handle.handleId == handleId {
						handle.nesting -= 1
						if handle.nesting == 0 {
							break
						}
					}
					fiber.frames[i] = handle
				default:
					continue
				}
			}
		case COMPLETE:
			handle := fiber.PopFrame().(HandleFrame)
			afterFrame := m.callClosureFrame(fiber, handle.afterClosure, &handle.VariableFrame, nil, handle.afterLocation)
			fiber.PushFrame(afterFrame)
			fiber.instruction = handle.afterClosure.codeStart
		case ESCAPE:
			handleId := int(m.ReadInt32(fiber))
			handlerInd := m.ReadUInt8(fiber)
			handleFrame, frameInd := fiber.FindFreeHandler(handleId)
			handler := handleFrame.handlers[handlerInd]
			captureFrameCount := uint(len(fiber.frames)) - frameInd

			if handler.resumeLimit == ResumeNever {
				// handler promises to never resume, so no need to capture the continuation
				handlerFrame := m.callClosureFrame(fiber, handler, &handleFrame.VariableFrame, nil, handleFrame.afterLocation)
				fiber.DropFrames(captureFrameCount)
				fiber.PushFrame(handlerFrame)
			} else if handler.resumeLimit == ResumeOnceTail {
				// handler promises to only resume at the end of it's execution, and does not thread parameters through the effect
				handlerFrame := m.callClosureFrame(fiber, handler, nil, nil, fiber.instruction)
				fiber.PushFrame(handlerFrame)
			} else {
				contParamCount := len(handleFrame.slots)
				cont := Continuation{
					fiber.instruction,
					uint(contParamCount),
					make([]Value, len(fiber.values)-contParamCount),
					make([]Frame, captureFrameCount)}
				copy(cont.savedValues, fiber.values[:len(fiber.values)-contParamCount])
				copy(cont.savedFrames, fiber.frames[:captureFrameCount])

				handlerFrame := m.callClosureFrame(fiber, handler, &handleFrame.VariableFrame, &cont, handleFrame.afterLocation)

				fiber.values = make([]Value, 0)
				fiber.DropFrames(captureFrameCount)
				fiber.PushFrame(handlerFrame)
			}

			fiber.instruction = handler.codeStart
		case CALL_CONTINUATION:
			cont := fiber.PopOneValue().(Continuation)
			handleFrame := cont.savedFrames[0].(HandleFrame)
			m.restoreSaved(fiber, handleFrame, cont, fiber.instruction)
			fiber.instruction = cont.resume
		case TAILCALL_CONTINUATION:
			cont := fiber.PopOneValue().(Continuation)
			handleFrame := cont.savedFrames[0].(HandleFrame)
			tailAfter := fiber.PopFrame().(CallFrame).afterLocation
			m.restoreSaved(fiber, handleFrame, cont, tailAfter)
			fiber.instruction = cont.resume

		case SHUFFLE:
			pop := m.ReadUInt8(fiber)
			push := int(m.ReadUInt8(fiber))
			popped := fiber.values[len(fiber.values)-1-int(pop):]
			newValues := fiber.values[:len(fiber.values)-1-int(pop)]
			for i := 0; i < push; i++ {
				ind := m.ReadUInt8(fiber)
				newValues = append(newValues, popped[ind])
			}
			fiber.values = newValues

		// REFERENCE VALUES
		case NEWREF:
			refInit := fiber.PopOneValue()
			// TODO: make these next two lines atomic/thread safe
			refKey := m.nextHeapKey
			m.nextHeapKey += 1
			m.heap[refKey] = refInit
			fiber.PushValue(Ref{refKey})
		case GETREF:
			ref := fiber.PopOneValue().(Ref)
			fiber.PushValue(m.heap[ref.pointer])
		case PUTREF:
			val := fiber.PopOneValue()
			ref := fiber.PopOneValue().(Ref)
			m.heap[ref.pointer] = val

		// COMPOSITE VALUES
		case CONSTRUCT:
			compositeId := CompositeId(m.ReadInt32(fiber))
			count := m.ReadUInt8(fiber)

			composite := Composite{compositeId, make([]Value, count)}
			// NOTE: this make the values in the struct ID conceptually 'backwards'
			// from how they were laid out on the stack, even though in memory its
			// the same order. The stack top pointer is at the end of the array, the
			// struct pointer is at the beginning. Doing it this way means we don't
			// have to reverse the elements, but might lead to conceptual confusion.
			// DOCUMENTATION REQUIRED
			copy(fiber.values[len(fiber.values)-int(count):], composite.elements)
			fiber.values = fiber.values[:len(fiber.values)-int(count)]
			fiber.PushValue(composite)
		case DESTRUCT:
			composite := fiber.PopOneValue().(Composite)
			// NOTE: see note in CONSTRUCT instruction for a potential conceptual
			// pitfall.
			fiber.values = append(fiber.values, composite.elements...)
		case IS_COMPOSITE:
			compositeId := CompositeId(m.ReadInt32(fiber))
			composite := fiber.PopOneValue().(Composite)
			fiber.PushValue(composite.id == compositeId)
		case JUMP_COMPOSITE:
			compositeId := CompositeId(m.ReadInt32(fiber))
			jump := CodePointer(m.ReadUInt32(fiber))
			composite := fiber.PopOneValue().(Composite)
			if composite.id == compositeId {
				fiber.instruction = jump
			}
		case OFFSET_COMPOSITE:
			compositeId := CompositeId(m.ReadInt32(fiber))
			offset := m.ReadInt32(fiber)
			composite := fiber.PopOneValue().(Composite)
			if composite.id == compositeId {
				// TODO: this int conversion seems bad
				fiber.instruction = CodePointer(int(fiber.instruction) + int(offset))
			}

		// RECORDS
		case RECORD_NIL:
			fiber.PushValue(Record{map[Label]Value{}})
		case RECORD_EXTEND:
			label := int(m.ReadInt32(fiber))
			val := fiber.PopOneValue()
			record := fiber.PopOneValue().(Record)
			fiber.PushValue(record.Extend(label, val))
		case RECORD_SELECT:
			label := int(m.ReadInt32(fiber))
			record := fiber.PopOneValue().(Record)
			fiber.PushValue(record.Select(label))
		case RECORD_RESTRICT:
			label := int(m.ReadInt32(fiber))
			record := fiber.PopOneValue().(Record)
			fiber.PushValue(record.Restrict(label))
		case RECORD_UPDATE:
			label := int(m.ReadInt32(fiber))
			val := fiber.PopOneValue()
			record := fiber.PopOneValue().(Record)
			fiber.PushValue(record.Update(label, val))

		// VARIANTS
		case VARIANT:
			label := int(m.ReadInt32(fiber))
			initial := fiber.PopOneValue()
			fiber.PushValue(Variant{Label{label, 0}, initial})
		case EMBED:
			label := int(m.ReadInt32(fiber))
			variant := fiber.PopOneValue().(Variant)
			fiber.PushValue(variant.Embed(label))
		case IS_CASE:
			label := int(m.ReadInt32(fiber))
			variant := fiber.PopOneValue().(Variant)
			fiber.PushValue(variant.label.labelName == label)
		case JUMP_CASE:
			label := int(m.ReadInt32(fiber))
			jump := CodePointer(m.ReadUInt32(fiber))
			variant := fiber.PopOneValue().(Variant)
			if variant.label.labelName == label {
				fiber.instruction = jump
			}
		case OFFSET_CASE:
			label := int(m.ReadInt32(fiber))
			offset := int(m.ReadInt32(fiber))
			variant := fiber.PopOneValue().(Variant)
			if variant.label.labelName == label {
				// TODO: this int conversion seems bad
				fiber.instruction = CodePointer(int(fiber.instruction) + offset)
			}
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
