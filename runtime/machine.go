package runtime

import (
	"fmt"
)

type HeapKey = uint

type CodePointer = uint

type NativeFn = func(*Machine, *Fiber)

type Machine struct {
	code      []byte
	lines     []uint
	constants []Value

	labels map[uint]string

	heap        map[HeapKey]Value
	nextHeapKey HeapKey

	nativeFns     []NativeFn
	nativeFnNames []string

	traceValues    bool
	traceFrames    bool
	traceExecution bool
}

func NewDebugMachine() *Machine {
	m := new(Machine)
	m.code = make([]byte, 0)
	m.lines = make([]uint, 0)
	m.constants = make([]Value, 0)

	m.labels = make(map[uint]string)
	m.heap = make(map[uint]Value)
	m.nextHeapKey = 0

	m.nativeFns = make([]NativeFn, 0)
	m.nativeFnNames = make([]string, 0)

	m.traceValues = true
	m.traceFrames = true
	m.traceExecution = true
	return m
}

func (m *Machine) RegisterNative(name string, fn NativeFn) {
	m.nativeFns = append(m.nativeFns, fn)
	m.nativeFnNames = append(m.nativeFnNames, name)
}

func (m *Machine) AddConstant(val Value) {
	m.constants = append(m.constants, val)
}

func (m *Machine) AddLabel(label string, index uint) {
	m.labels[index] = label
}

func (m *Machine) RunFromStart() int32 {
	fiber := new(Fiber)
	fiber.instruction = 0
	fiber.values = make([]Value, 0)
	fiber.frames = make([]Frame, 0)
	fiber.roots = make([]Value, 0)
	fiber.caller = nil

	if m.traceExecution {
		m.Disassemble()
	}

	return m.Run(fiber)
}

func (m *Machine) Run(fiber *Fiber) int32 {
	for {
		if m.traceValues {
			m.PrintFiberValueStack(fiber)
		}
		if m.traceFrames {
			m.PrintFiberFrameStack(fiber)
		}
		if m.traceExecution {
			m.DisassembleInstruction(fiber.instruction)
		}

		switch fiber.ReadInstruction(m) {
		case NOP:
			// do nothing
		case BREAKPOINT:
			panic("BREAKPOINT is not yet implemented.")
		case ABORT:
			result := fiber.PopOneValue().(int32)
			return result
		case CONSTANT:
			constIdx := fiber.ReadUInt16(m)
			fiber.PushValue(m.constants[constIdx])

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
			fiber.PushValue(fiber.ReadInt8(m))
		case U8:
			fiber.PushValue(fiber.ReadUInt8(m))
		case I16:
			fiber.PushValue(fiber.ReadInt16(m))
		case U16:
			fiber.PushValue(fiber.ReadUInt16(m))
		case I32:
			fiber.PushValue(fiber.ReadInt32(m))
		case U32:
			fiber.PushValue(fiber.ReadUInt32(m))
		case I64:
			fiber.PushValue(fiber.ReadInt64(m))
		case U64:
			fiber.PushValue(fiber.ReadUInt64(m))
		case SINGLE:
			fiber.PushValue(fiber.ReadSingle(m))
		case DOUBLE:
			fiber.PushValue(fiber.ReadDouble(m))

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
			from := fiber.ReadUInt8(m)
			to := fiber.ReadUInt8(m)
			val := fiber.PopOneValue()
			switch from {
			case BOOL:
				fiber.PushValue(convertBool(val.(bool), to))
			case I8:
				fiber.PushValue(convertI8(val.(int8), to))
			case U8:
				fiber.PushValue(convertU8(val.(uint8), to))
			case I16:
				fiber.PushValue(convertI16(val.(int16), to))
			case U16:
				fiber.PushValue(convertU16(val.(uint16), to))
			case I32:
				fiber.PushValue(convertI32(val.(int32), to))
			case U32:
				fiber.PushValue(convertU32(val.(uint32), to))
			case I64:
				fiber.PushValue(convertI64(val.(int64), to))
			case U64:
				fiber.PushValue(convertU64(val.(uint64), to))
			case INATIVE:
				fiber.PushValue(convertINative(val.(int), to))
			case UNATIVE:
				fiber.PushValue(convertUNative(val.(uint), to))
			case SINGLE:
				fiber.PushValue(convertSingle(val.(float32), to))
			case DOUBLE:
				fiber.PushValue(convertDouble(val.(float64), to))
			default:
				panic("Unimplemented value type in conversion.")
			}

		// VARIABLE FRAME OPERATIONS
		case STORE:
			varCount := int(fiber.ReadUInt8(m))
			fiber.StoreVars(varCount)
		case FIND:
			frameIdx := fiber.ReadUInt16(m)
			slotIdx := fiber.ReadUInt16(m)
			frame := fiber.PeekFrameAt(uint(frameIdx))
			fiber.PushValue(frame.Slots()[slotIdx])
		case OVERWRITE:
			frameIdx := fiber.ReadUInt16(m)
			slotIdx := fiber.ReadUInt16(m)
			frame := fiber.PeekFrameAt(uint(frameIdx))
			frame.Slots()[slotIdx] = fiber.PopOneValue()
		case FORGET:
			fiber.PopFrame()

		// FUNCTION AND CLOSURE CALL RELATED
		case CALL_NATIVE:
			fnIndex := fiber.ReadUInt16(m)
			fn := m.nativeFns[fnIndex]
			fn(m, fiber)
		case CALL:
			fnStart := fiber.ReadUInt32(m)
			frame := CallFrame{VariableFrame{make([]Value, 0)}, fiber.instruction}
			fiber.PushFrame(frame)
			fiber.instruction = uint(fnStart)
		case TAILCALL:
			fiber.instruction = uint(fiber.ReadUInt32(m))
		case CALL_CLOSURE:
			closure := fiber.PopOneValue().(Closure)
			frame := fiber.SetupClosureCall(closure, nil, nil, fiber.instruction)
			fiber.PushFrame(frame)
			fiber.instruction = closure.codeStart
		case TAILCALL_CLOSURE:
			closure := fiber.PopOneValue().(Closure)
			frame := fiber.SetupClosureCall(closure, nil, nil, fiber.PeekFrameAt(1).(CallFrame).afterLocation)
			fiber.PopFrame()
			fiber.PushFrame(frame)
			fiber.instruction = closure.codeStart
		case OFFSET:
			offset := fiber.ReadInt32(m)
			// TODO: this int() conversion is a bit bad
			fiber.instruction = uint(int32(fiber.instruction) + offset)
		case RETURN:
			frame := fiber.PopFrame().(CallFrame)
			fiber.instruction = frame.afterLocation

		// CONDITIONAL JUMPS
		case JUMP_TRUE:
			jump := fiber.ReadUInt32(m)
			if fiber.PopOneValue().(bool) {
				fiber.instruction = uint(jump)
			}
		case JUMP_FALSE:
			jump := fiber.ReadUInt32(m)
			if !fiber.PopOneValue().(bool) {
				fiber.instruction = uint(jump)
			}
		case OFFSET_TRUE:
			offset := fiber.ReadInt32(m)
			if fiber.PopOneValue().(bool) {
				// TODO: this int() conversion is a bit bad
				fiber.instruction = uint(int(offset) + int(fiber.instruction))
			}
		case OFFSET_FALSE:
			offset := fiber.ReadInt32(m)
			if !fiber.PopOneValue().(bool) {
				// TODO: this int() conversion is a bit bad
				fiber.instruction = uint(int(offset) + int(fiber.instruction))
			}

		// CLOSURE BUILDING
		case CLOSURE:
			codeStart := fiber.ReadUInt32(m)
			paramCount := fiber.ReadUInt8(m)
			closedCount := fiber.ReadUInt16(m)

			closure := Closure{CodePointer(codeStart), uint(paramCount), ResumeMany, make([]Value, closedCount)}
			for i := 0; i < int(closedCount); i++ {
				frameInd := fiber.ReadUInt16(m)
				slotInd := fiber.ReadUInt16(m)
				frame := fiber.frames[len(fiber.frames)-1-int(frameInd)]
				closure.captured[i] = frame.Slots()[slotInd]
			}
			fiber.PushValue(closure)
		case RECURSIVE:
			codeStart := fiber.ReadUInt32(m)
			paramCount := fiber.ReadUInt8(m)
			closedCount := fiber.ReadUInt16(m)

			closure := Closure{CodePointer(codeStart), uint(paramCount), ResumeMany, make([]Value, closedCount+1)}
			closure.captured[0] = closure
			for i := 0; i < int(closedCount); i++ {
				frameInd := fiber.ReadUInt16(m)
				slotInd := fiber.ReadUInt16(m)
				frame := fiber.frames[len(fiber.frames)-1-int(frameInd)]
				closure.captured[i+1] = frame.Slots()[slotInd]
			}
			fiber.PushValue(closure)
		case MUTUAL:
			mutualCount := int(fiber.ReadUInt8(m))
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
			after := int(fiber.ReadInt16(m))
			handleId := int(fiber.ReadInt32(m))
			paramCount := uint(fiber.ReadUInt8(m))
			handlerCount := uint(fiber.ReadUInt8(m))

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
			handleId := int(fiber.ReadInt32(m))
			for i := len(fiber.frames) - 1; i >= 0; i-- {
				frame := fiber.frames[i]
				switch frame := frame.(type) {
				case HandleFrame:
					if frame.handleId == handleId {
						frame.nesting += 1
						if frame.nesting == 1 {
							break
						}
					}
					fiber.frames[i] = frame
				default:
					continue
				}
			}
		case EJECT:
			handleId := int(fiber.ReadInt32(m))
			for i := len(fiber.frames) - 1; i >= 0; i-- {
				frame := fiber.frames[i]
				switch frame := frame.(type) {
				case HandleFrame:
					if frame.handleId == handleId {
						frame.nesting -= 1
						if frame.nesting == 0 {
							break
						}
					}
					fiber.frames[i] = frame
				default:
					continue
				}
			}
		case COMPLETE:
			handle := fiber.PopFrame().(HandleFrame)
			afterFrame := fiber.SetupClosureCall(handle.afterClosure, &handle.VariableFrame, nil, handle.afterLocation)
			fiber.PushFrame(afterFrame)
			fiber.instruction = handle.afterClosure.codeStart
		case ESCAPE:
			handleId := int(fiber.ReadInt32(m))
			handlerInd := fiber.ReadUInt8(m)
			handleFrame, captureFrameCount := fiber.FindFreeHandler(handleId)
			handler := handleFrame.handlers[handlerInd]

			if handler.resumeLimit == ResumeNever {
				// handler promises to never resume, so no need to capture the continuation
				handlerFrame := fiber.SetupClosureCall(handler, &handleFrame.VariableFrame, nil, handleFrame.afterLocation)
				fiber.DropFrames(captureFrameCount)
				fiber.PushFrame(handlerFrame)
			} else if handler.resumeLimit == ResumeOnceTail {
				// handler promises to only resume at the end of it's execution, and does not thread parameters through the effect
				handlerFrame := fiber.SetupClosureCall(handler, nil, nil, fiber.instruction)
				fiber.PushFrame(handlerFrame)
			} else {
				contParamCount := len(handleFrame.slots)
				captureValCount := len(fiber.values) - int(handler.paramCount)
				cont := Continuation{
					fiber.instruction,
					uint(contParamCount),
					make([]Value, captureValCount),
					make([]Frame, captureFrameCount)}
				copy(cont.savedValues, fiber.values[:captureValCount])
				copy(cont.savedFrames, fiber.frames[captureFrameCount:])

				handlerFrame := fiber.SetupClosureCall(handler, &handleFrame.VariableFrame, &cont, handleFrame.afterLocation)

				fiber.values = make([]Value, 0)
				fiber.DropFrames(captureFrameCount)
				fiber.PushFrame(handlerFrame)
			}

			fiber.instruction = handler.codeStart
		case CALL_CONTINUATION:
			cont := fiber.PopOneValue().(Continuation)
			handleFrame := cont.savedFrames[0].(HandleFrame)
			fiber.RestoreSaved(handleFrame, cont, fiber.instruction)
			fiber.instruction = cont.resume
		case TAILCALL_CONTINUATION:
			cont := fiber.PopOneValue().(Continuation)
			handleFrame := cont.savedFrames[0].(HandleFrame)
			tailAfter := fiber.PopFrame().(CallFrame).afterLocation
			fiber.RestoreSaved(handleFrame, cont, tailAfter)
			fiber.instruction = cont.resume

		case SWAP:
			fst := fiber.PopOneValue()
			snd := fiber.PopOneValue()
			fiber.PushValue(fst)
			fiber.PushValue(snd)
		case DUP:
			val := fiber.PopOneValue()
			fiber.PushValue(val)
			fiber.PushValue(val)
		case ZAP:
			fiber.PopOneValue()
		case SHUFFLE:
			pop := fiber.ReadUInt8(m)
			push := int(fiber.ReadUInt8(m))
			popped := fiber.values[len(fiber.values)-1-int(pop):]
			newValues := make([]Value, 0)
			copy(newValues, fiber.values[:len(fiber.values)-1-int(pop)])
			for i := 0; i < push; i++ {
				ind := fiber.ReadUInt8(m)
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
			compositeId := CompositeId(fiber.ReadInt32(m))
			count := fiber.ReadUInt8(m)

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
			compositeId := CompositeId(fiber.ReadInt32(m))
			composite := fiber.PopOneValue().(Composite)
			fiber.PushValue(composite.id == compositeId)
		case JUMP_COMPOSITE:
			compositeId := CompositeId(fiber.ReadInt32(m))
			jump := CodePointer(fiber.ReadUInt32(m))
			composite := fiber.PopOneValue().(Composite)
			if composite.id == compositeId {
				fiber.instruction = jump
			}
		case OFFSET_COMPOSITE:
			compositeId := CompositeId(fiber.ReadInt32(m))
			offset := fiber.ReadInt32(m)
			composite := fiber.PopOneValue().(Composite)
			if composite.id == compositeId {
				// TODO: this int conversion seems bad
				fiber.instruction = CodePointer(int(fiber.instruction) + int(offset))
			}

		// RECORDS
		case RECORD_NIL:
			fiber.PushValue(make(map[int]Value))
		case RECORD_EXTEND:
			label := int(fiber.ReadInt32(m))
			val := fiber.PopOneValue()
			record := fiber.PopOneValue().(map[int]Value)
			newRec := make(map[int]Value)
			for k, v := range record {
				newRec[k] = v
			}
			newRec[label] = val
			fiber.PushValue(newRec)
		case RECORD_SELECT:
			label := int(fiber.ReadInt32(m))
			record := fiber.PopOneValue().(map[int]Value)
			fiber.PushValue(record[label])

		// VARIANTS
		case VARIANT:
			label := int(fiber.ReadInt32(m))
			initial := fiber.PopOneValue()
			fiber.PushValue(Variant{label, initial})
		case IS_CASE:
			label := int(fiber.ReadInt32(m))
			variant := fiber.PopOneValue().(Variant)
			fiber.PushValue(variant.label == label)
		case JUMP_CASE:
			label := int(fiber.ReadInt32(m))
			jump := CodePointer(fiber.ReadUInt32(m))
			variant := fiber.PopOneValue().(Variant)
			if variant.label == label {
				fiber.instruction = jump
			}
		case OFFSET_CASE:
			label := int(fiber.ReadInt32(m))
			offset := int(fiber.ReadInt32(m))
			variant := fiber.PopOneValue().(Variant)
			if variant.label == label {
				// TODO: this int conversion seems bad
				fiber.instruction = CodePointer(int(fiber.instruction) + offset)
			}

		case ARRAY_NIL:
			arr := make([]Value, 0)
			fiber.PushValue(arr)
		case ARRAY_CONS:
			val := fiber.PopOneValue()
			arr := fiber.PopOneValue().([]Value)
			newArr := make([]Value, len(arr)-1)
			copy(newArr, arr)
			newArr[len(arr)] = val
		case ARRAY_BREAK:
			arr := fiber.PopOneValue().([]Value)
			fiber.PushValue(arr[:len(arr)-1])
			fiber.PushValue(arr[len(arr)-1])
		case ARRAY_HEAD:
			arr := fiber.PopOneValue().([]Value)
			fiber.PushValue(arr[len(arr)-1])
		case ARRAY_TAIL:
			arr := fiber.PopOneValue().([]Value)
			fiber.PushValue(arr[:len(arr)-1])

		case STRING_CONCAT:
			right := fiber.PopOneValue().(string)
			left := fiber.PopOneValue().(string)
			fiber.PushValue(left + right)
		case PRINT:
			str := fiber.PopOneValue().(string)
			fmt.Print(str)
		}
	}
}

func (m *Machine) UnaryNumeric(fiber *Fiber, unary func(Instruction, Value) Value) {
	fiber.PushValue(unary(fiber.ReadInstruction(m), fiber.PopOneValue()))
}

func (m *Machine) BinaryNumeric(fiber *Fiber, binary func(Instruction, Value, Value) Value) {
	l, r := fiber.PopTwoValues()
	fiber.PushValue(binary(fiber.ReadInstruction(m), l, r))
}

func (m *Machine) BinaryNumericBinaryOut(fiber *Fiber, binary func(Instruction, Value, Value) (Value, Value)) {
	l, r := fiber.PopTwoValues()
	b, t := binary(fiber.ReadInstruction(m), l, r)
	fiber.PushValue(b)
	fiber.PushValue(t)
}

func (m *Machine) PrintFiberValueStack(f *Fiber) {
	fmt.Printf("VALUES:    ")
	if len(f.values) <= 0 {
		fmt.Printf("<empty>")
	}
	for _, v := range f.values {
		fmt.Printf("[")
		m.PrintValue(v)
		fmt.Printf("]")
	}
	fmt.Println()
}

func (m *Machine) PrintFiberFrameStack(f *Fiber) {
	fmt.Printf("FRAMES:    ")
	if len(f.frames) <= 0 {
		fmt.Printf("<empty>")
	}
	for _, v := range f.frames {
		fmt.Printf("[")
		m.PrintFrame(v)
		fmt.Printf("]")
	}
	fmt.Println()
}

func (m *Machine) PrintValue(v Value) {
	switch v := v.(type) {
	case Closure:
		fmt.Printf("closure(%d [", v.codeStart)
		for _, v := range v.captured {
			m.PrintValue(v)
			fmt.Printf(", ")
		}
		fmt.Printf("])")
	case Continuation:
		fmt.Printf("cont(%d -> %d [", v.paramCount, v.resume)
		for _, v := range v.savedValues {
			m.PrintValue(v)
			fmt.Printf(",")
		}
		fmt.Printf("] [")
		for _, f := range v.savedFrames {
			m.PrintTinyFrame(f)
			fmt.Printf(",")
		}
		fmt.Printf("])")
	case Ref:
		fmt.Printf("ref(%d: ", v.pointer)
		m.PrintValue(m.heap[v.pointer])
		fmt.Print(")")
	case Composite:
		fmt.Printf("cmp(%d: ", v.id)
		for v := range v.elements {
			m.PrintValue(v)
			fmt.Print(", ")
		}
	case Variant:
		fmt.Printf("var(%v: ", v.label)
		m.PrintValue(v.value)
		fmt.Printf(")")
	case ValueArray:
		fmt.Print("arr(")
		for e := range v.elements {
			m.PrintValue(e)
			fmt.Print(", ")
		}
	default:
		fmt.Print(v)
	}
}

func (m *Machine) PrintFrame(f Frame) {
	switch f := f.(type) {
	case VariableFrame:
		fmt.Printf("var(%d)", len(f.slots))
	case CallFrame:
		fmt.Printf("call(%d [", f.afterLocation)
		for _, v := range f.slots {
			m.PrintValue(v)
			fmt.Printf(",")
		}
		fmt.Printf("])")
	case HandleFrame:
		fmt.Printf("handle(%d: n(%d) %d %d -> %d)", f.handleId, f.nesting, len(f.handlers), len(f.slots), f.afterLocation)
	}
}

func (m *Machine) PrintTinyFrame(f Frame) {
	switch f.(type) {
	case VariableFrame:
		fmt.Printf("var")
	case CallFrame:
		fmt.Printf("call")
	case HandleFrame:
		fmt.Printf("handle")
	}
}
