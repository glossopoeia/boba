package runtime

import (
	"bufio"
	"context"
	"fmt"
	"os"
	"strings"
	"sync"
)

type HeapKey = uint

type CodePointer = uint

type NativeFn = func(*Machine, *Fiber)

const (
	PERMISSION_UNCHECKED int = iota
	PERMISSION_ALLOWED
	PERMISSION_DENIED
)

const (
	PERM_CONSOLE int = iota
	PERM_NETWORK
)

type Machine struct {
	code        []byte
	lines       []uint
	constants   []Value
	permissions map[int]int

	labels map[uint]string

	Heap        map[HeapKey]Value
	NextHeapKey HeapKey

	nativeFns     []NativeFn
	nativeFnNames []string

	TraceValues    bool
	TraceFrames    bool
	TraceExecution bool

	nextFiberId int
}

func NewDebugMachine() *Machine {
	m := new(Machine)
	m.code = make([]byte, 0)
	m.lines = make([]uint, 0)
	m.constants = make([]Value, 0)

	m.permissions = map[int]int{
		PERM_CONSOLE: PERMISSION_UNCHECKED,
		PERM_NETWORK: PERMISSION_UNCHECKED,
	}

	m.labels = make(map[uint]string)
	m.Heap = make(map[uint]Value)
	m.NextHeapKey = 0

	m.nativeFns = make([]NativeFn, 0)
	m.nativeFnNames = make([]string, 0)

	m.TraceValues = true
	m.TraceFrames = true
	m.TraceExecution = true

	m.nextFiberId = 0
	return m
}

func NewReleaseMachine() *Machine {
	m := new(Machine)
	m.code = make([]byte, 0)
	m.lines = make([]uint, 0)
	m.constants = make([]Value, 0)

	m.permissions = map[int]int{
		PERM_CONSOLE: PERMISSION_UNCHECKED,
		PERM_NETWORK: PERMISSION_UNCHECKED,
	}

	m.labels = make(map[uint]string)
	m.Heap = make(map[uint]Value)
	m.NextHeapKey = 0

	m.nativeFns = make([]NativeFn, 0)
	m.nativeFnNames = make([]string, 0)

	m.TraceValues = false
	m.TraceFrames = false
	m.TraceExecution = false

	m.nextFiberId = 0
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

func (m *Machine) RunFromStart() int {
	fiber := NewFiber(m, nil, []Context{{context.Background()}})

	if m.TraceExecution {
		m.Disassemble()
	}

	return m.Run(fiber)
}

func (m *Machine) RunSub(fiber *Fiber, wg *sync.WaitGroup) {
	m.Run(fiber)
	wg.Done()
}

func (m *Machine) Run(fiber *Fiber) int {
	for {
		if m.TraceValues {
			m.PrintFiberStack(fiber)
			m.PrintFiberValueStack(fiber)
		}
		if m.TraceFrames {
			m.PrintStoredStack(fiber)
			m.PrintAftersStack(fiber)
			m.PrintMarksStack(fiber)
		}
		if m.TraceExecution {
			m.DisassembleInstruction(fiber.Instruction)
		}
		if fiber.Cancelled {
			return -1
		}

		switch fiber.ReadInstruction(m) {
		case NOP:
			// do nothing
		case BREAKPOINT:
			panic("BREAKPOINT is not yet implemented.")
		case ABORT:
			result := fiber.PopOneValue().(int)
			return result
		case CONSTANT:
			constIdx := fiber.ReadUInt16(m)
			fiber.PushValue(m.constants[constIdx])

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
		case INATIVE:
			fiber.PushValue(fiber.ReadInt(m))
		case UNATIVE:
			fiber.PushValue(fiber.ReadUInt(m))
		case SINGLE:
			fiber.PushValue(fiber.ReadSingle(m))
		case DOUBLE:
			fiber.PushValue(fiber.ReadDouble(m))
		case RUNE:
			fiber.PushValue(rune(fiber.ReadInt32(m)))

		// NUMERIC OPERATIONS
		case NUM_DIV_REM_T:
			m.BinaryNumericBinaryOut(fiber, DivRemT)
		case NUM_DIV_REM_F:
			m.BinaryNumericBinaryOut(fiber, DivRemF)
		case NUM_DIV_REM_E:
			m.BinaryNumericBinaryOut(fiber, DivRemE)
		case INT_COMP:
			m.UnaryNumeric(fiber, Complement)
		case NUM_SIGN:
			m.UnaryNumeric(fiber, Sign)

		// VARIABLE FRAME OPERATIONS
		case STORE:
			varCount := int(fiber.ReadUInt8(m))
			valsLen := len(fiber.values)
			if valsLen < varCount {
				panic("STORE: Not enough values to store in frame")
			}
			fiber.Stored = append(fiber.Stored, fiber.values[len(fiber.values)-varCount:]...)
			fiber.values = fiber.values[:len(fiber.values)-varCount]
		case FIND:
			varInd := uint(fiber.ReadUInt32(m))
			fiber.PushValue(fiber.Stored[uint(len(fiber.Stored))-varInd-1])
		case OVERWRITE:
			varInd := uint(fiber.ReadUInt32(m))
			fiber.Stored[uint(len(fiber.Stored))-varInd-1] = fiber.PopOneValue()
		case FORGET:
			varCount := int(fiber.ReadUInt8(m))
			fiber.Stored = fiber.Stored[:len(fiber.Stored)-varCount]

		// FUNCTION AND CLOSURE CALL RELATED
		case CALL_NATIVE:
			fnIndex := fiber.ReadUInt32(m)
			fn := m.nativeFns[fnIndex]
			fn(m, fiber)
		case CALL:
			fnStart := fiber.ReadUInt32(m)
			fiber.afters = append(fiber.afters, fiber.Instruction)
			fiber.Instruction = uint(fnStart)
		case TAILCALL:
			fiber.Instruction = uint(fiber.ReadUInt32(m))
		case CALL_CLOSURE:
			closure := fiber.PopOneValue().(Closure)
			fiber.Stored = append(fiber.Stored, closure.Captured...)
			// push return location and jump to new location
			fiber.afters = append(fiber.afters, fiber.Instruction)
			fiber.Instruction = closure.CodeStart
		case TAILCALL_CLOSURE:
			closure := fiber.PopOneValue().(Closure)
			fiber.Stored = append(fiber.Stored, closure.Captured...)
			// push return location and jump to new location
			fiber.afters = append(fiber.afters, fiber.PopAfter())
			fiber.Instruction = closure.CodeStart
		case OFFSET:
			offset := fiber.ReadInt32(m)
			// TODO: this int() conversion is a bit bad
			fiber.Instruction = uint(int32(fiber.Instruction) + offset)
		case RETURN:
			// TODO: this is used for closures in a SPAWN call, might need a better way of handling this?
			// TODO: could make a `spawn { ... }` syntax that gets compiled with special ABORT code at the
			//       end of the body expression
			if len(fiber.afters) <= 0 {
				return -1
			}
			fiber.Instruction = fiber.PopAfter()

		// CONDITIONAL JUMPS
		case JUMP_TRUE:
			jump := fiber.ReadUInt32(m)
			if fiber.PopOneValue().(bool) {
				fiber.Instruction = uint(jump)
			}
		case JUMP_FALSE:
			jump := fiber.ReadUInt32(m)
			if !fiber.PopOneValue().(bool) {
				fiber.Instruction = uint(jump)
			}
		case OFFSET_TRUE:
			offset := fiber.ReadInt32(m)
			if fiber.PopOneValue().(bool) {
				// TODO: this int() conversion is a bit bad
				fiber.Instruction = uint(int(offset) + int(fiber.Instruction))
			}
		case OFFSET_FALSE:
			offset := fiber.ReadInt32(m)
			if !fiber.PopOneValue().(bool) {
				// TODO: this int() conversion is a bit bad
				fiber.Instruction = uint(int(offset) + int(fiber.Instruction))
			}

		// CLOSURE BUILDING
		case CLOSURE:
			codeStart := fiber.ReadUInt32(m)
			closedCount := fiber.ReadUInt16(m)

			closure := Closure{CodePointer(codeStart), ResumeMany, make([]Value, closedCount)}
			for i := 0; i < int(closedCount); i++ {
				// the distance the variable value is from the top of the variable stack
				varInd := fiber.ReadUInt32(m)
				varVal := fiber.Stored[len(fiber.Stored)-1-int(varInd)]
				closure.Captured[i] = varVal
			}
			fiber.PushValue(closure)
		case RECURSIVE:
			codeStart := fiber.ReadUInt32(m)
			closedCount := fiber.ReadUInt16(m)

			closure := Closure{CodePointer(codeStart), ResumeMany, make([]Value, closedCount+1)}
			closure.Captured[0] = closure
			for i := 0; i < int(closedCount); i++ {
				// the distance the variable value is from the top of the variable stack
				varInd := fiber.ReadUInt32(m)
				varVal := fiber.Stored[len(fiber.Stored)-1-int(varInd)]
				closure.Captured[i+1] = varVal
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
				newC := Closure{oldC.CodeStart, oldC.ResumeLimit, make([]Value, len(oldC.Captured)+mutualCount)}
				copy(newC.Captured[mutualCount:len(newC.Captured)], oldC.Captured)
				fiber.values[oldCInd] = newC
			}
			// finally, make the closures all reference each other in the same order
			for i := 0; i < mutualCount; i++ {
				recC := fiber.values[len(fiber.values)-1-i].(Closure)
				copy(fiber.values[len(fiber.values)-mutualCount:len(fiber.values)], recC.Captured[:mutualCount-1])
				fiber.values[len(fiber.values)-1-i] = recC
			}
		case CLOSURE_ONCE:
			closure := fiber.PopOneValue().(Closure)
			closure.ResumeLimit = ResumeOnce
			fiber.PushValue(closure)
		case CLOSURE_ONCE_TAIL:
			closure := fiber.PopOneValue().(Closure)
			closure.ResumeLimit = ResumeOnceTail
			fiber.PushValue(closure)
		case CLOSURE_NEVER:
			closure := fiber.PopOneValue().(Closure)
			closure.ResumeLimit = ResumeNever
			fiber.PushValue(closure)

		// CONCURRENCY
		case NEW_NURSERY:
			wg := new(sync.WaitGroup)
			fiber.PushValue(Nursery{wg})
		case WAIT_NURSERY:
			wg := fiber.PopOneValue().(Nursery).Waiter
			wg.Wait()
		case PUSH_CANCEL:
			ctx := fiber.LastCancelContext()
			newCtx, token := context.WithCancel(ctx.Ctx)
			fiber.PushValue(CancelToken{token})
			fiber.PushContext(newCtx)
		case POP_CONTEXT:
			fiber.PopContext()

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

			fiber.Stored = append(fiber.Stored, fiber.values[len(fiber.values)-int(paramCount):]...)
			fiber.values = fiber.values[:len(fiber.values)-int(paramCount)]

			marker := Marker{
				// TODO: this int() conversion is a bit bad
				uint(int(fiber.Instruction) + after),
				handleId,
				0,
				handlers,
				nil,
				len(fiber.values),
				len(fiber.Stored),
				len(fiber.afters),
			}
			fiber.PushMarker(marker)
		case INJECT:
			markId := int(fiber.ReadInt32(m))
			for i := len(fiber.marks) - 1; i >= 0; i-- {
				marker := fiber.marks[i]
				if marker.markId == markId {
					marker.nesting += 1
					if marker.nesting == 1 {
						break
					}
				}
				fiber.marks[i] = marker
			}
		case EJECT:
			markId := int(fiber.ReadInt32(m))
			for i := len(fiber.marks) - 1; i >= 0; i-- {
				marker := fiber.marks[i]
				if marker.markId == markId {
					marker.nesting -= 1
					if marker.nesting == 0 {
						break
					}
				}
				fiber.marks[i] = marker
			}
		case COMPLETE:
			markerInd := fiber.caller.FindFreeMarker(*fiber.HandlerId)
			marker := fiber.caller.marks[markerInd]
			fiber.caller.Instruction = marker.afterComplete
			fiber.caller.values = append(fiber.caller.values[:marker.valuesMark], fiber.values...)
			fiber.caller.Stored = fiber.caller.Stored[:marker.storedMark]
			// this line helps propagate handler parameters back to the source
			copy(fiber.caller.Stored[:marker.storedMark], fiber.Stored[:marker.storedMark])
			fiber.caller.afters = fiber.caller.afters[:marker.aftersMark]
			fiber.caller.marks = fiber.caller.marks[:markerInd+1]
			fiber = fiber.caller
		case ESCAPE:
			handleId := int(fiber.ReadInt32(m))
			handlerInd := fiber.ReadUInt8(m)
			inputs := fiber.ReadUInt8(m)
			m.Escape(&fiber, handleId, int(handlerInd), int(inputs))
		case CALL_CONTINUATION:
			outputs := fiber.ReadUInt8(m)
			threaded := fiber.ReadUInt8(m)
			cont := fiber.PopOneValue().(*Fiber)

			markerInd := cont.FindFreeMarker(*fiber.HandlerId)
			clonedResume := cont.CloneFiber(m, fiber)
			storedMark := clonedResume.marks[markerInd].storedMark
			clonedResume.marks[markerInd].finisher = fiber
			// pass on handle thread parameters
			copy(clonedResume.Stored[storedMark-int(threaded):], fiber.values[len(fiber.values)-int(threaded):])
			fiber.values = fiber.values[:len(fiber.values)-int(threaded)]
			// pass on the value parameters
			clonedResume.values = append(clonedResume.values, fiber.values[len(fiber.values)-int(outputs):]...)
			fiber.values = fiber.values[:len(fiber.values)-int(outputs)]
			fiber = clonedResume
		case TAILCALL_CONTINUATION:
			outputs := fiber.ReadUInt8(m)
			threaded := fiber.ReadUInt8(m)
			cont := fiber.PopOneValue().(*Fiber)

			markerInd := cont.FindFreeMarker(*fiber.HandlerId)
			storedMark := cont.marks[markerInd].storedMark
			cont.marks[markerInd].finisher = nil
			// pass on handle thread parameters
			copy(cont.Stored[storedMark-int(threaded):], fiber.values[len(fiber.values)-int(threaded):])
			fiber.values = fiber.values[:len(fiber.values)-int(threaded)]
			// pass on the value parameters
			cont.values = append(cont.values, fiber.values[len(fiber.values)-int(outputs):]...)
			fiber.values = fiber.values[:len(fiber.values)-int(outputs)]
			fiber = cont
		case RESTORE:
			marker := fiber.PopMarker()
			restored := marker.finisher
			if restored != nil {
				marker.finisher = nil
				restored.values = append(restored.values, fiber.values[marker.valuesMark:]...)
				fiber.values = fiber.values[:marker.valuesMark]
				copy(restored.Stored[:marker.storedMark], fiber.Stored[:marker.storedMark])
				fiber = restored
			}

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

		case HAS_PERMISSION:
			permId := fiber.ReadInt32(m)
			fiber.PushValue(m.permissions[int(permId)] == PERMISSION_ALLOWED)
		case REQUEST_PERMISSION:
			permId := fiber.ReadInt32(m)
			if m.permissions[int(permId)] == PERMISSION_ALLOWED {
				fiber.PushValue(true)
			} else {
				reader := bufio.NewReader(os.Stdin)
				fmt.Printf("Grant permission for %d? (yes/no): ", permId)
				text, err := reader.ReadString('\n')
				if err != nil {
					fmt.Printf("Permission request encountered an error, temporarily denying.")
					fiber.PushValue(false)
				} else {
					fiber.PushValue(strings.HasPrefix(text, "yes"))
				}
			}

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
			copy(composite.elements, fiber.values[len(fiber.values)-int(count):])
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
				fiber.Instruction = jump
			}
		case OFFSET_COMPOSITE:
			compositeId := CompositeId(fiber.ReadInt32(m))
			offset := fiber.ReadInt32(m)
			composite := fiber.PopOneValue().(Composite)
			if composite.id == compositeId {
				// TODO: this int conversion seems bad
				fiber.Instruction = CodePointer(int(fiber.Instruction) + int(offset))
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
				fiber.Instruction = jump
			}
		case OFFSET_CASE:
			label := int(fiber.ReadInt32(m))
			offset := int(fiber.ReadInt32(m))
			variant := fiber.PopOneValue().(Variant)
			if variant.label == label {
				// TODO: this int conversion seems bad
				fiber.Instruction = CodePointer(int(fiber.Instruction) + offset)
				fiber.PushValue(variant.value)
			} else {
				fiber.PushValue(variant)
			}
		}
	}
}

func (m *Machine) Escape(activeFiber **Fiber, handleId int, handlerInd int, inputs int) {
	fiber := *activeFiber
	capturedStartIndex := fiber.FindFreeMarker(handleId)
	marker := fiber.marks[capturedStartIndex]
	handler := marker.handlers[handlerInd]

	// create new fiber from where handler started
	cloned := fiber.CloneFiber(m, fiber)
	cloned.HandlerId = new(int)
	*cloned.HandlerId = handleId
	cloned.Instruction = handler.CodeStart
	cloned.Stored = cloned.Stored[:marker.storedMark]
	cloned.afters = cloned.afters[:marker.aftersMark]
	cloned.marks = cloned.marks[:capturedStartIndex]

	// put captured variables in environment
	cloned.Stored = append(cloned.Stored, handler.Captured...)

	// consume the required values from the calling fiber
	cloned.values = make([]Value, inputs)
	copy(cloned.values, fiber.values[len(fiber.values)-int(inputs):])
	fiber.values = fiber.values[:len(fiber.values)-int(inputs)]

	// make the current fiber available as a 'continuation' to the cloned one
	cloned.Stored = append(cloned.Stored, fiber)

	// add a marker finisher to get back here
	marker.finisher = fiber

	*activeFiber = cloned
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

func (m *Machine) PrintFiberStack(f *Fiber) {
	fib := f
	fmt.Printf("FIBERS:    ")
	for fib != nil {
		m.PrintValue(fib)
		fmt.Printf(" - ")
		fib = fib.caller
	}
	fmt.Println()
}

func (m *Machine) PrintFiberValueStack(f *Fiber) {
	fmt.Printf("VALUES:    ")
	if len(f.values) <= 0 {
		fmt.Printf("<empty>")
	}
	for _, v := range f.values {
		m.PrintValue(v)
		fmt.Printf(" ~ ")
	}
	fmt.Println()
}

func (m *Machine) PrintStoredStack(f *Fiber) {
	fmt.Printf("STORED:    ")
	if len(f.Stored) <= 0 {
		fmt.Printf("<empty>")
	}
	for _, v := range f.Stored {
		m.PrintValue(v)
		fmt.Printf(" ~ ")
	}
	fmt.Println()
}

func (m *Machine) PrintAftersStack(f *Fiber) {
	fmt.Printf("AFTERS:    ")
	if len(f.afters) <= 0 {
		fmt.Printf("<empty>")
	}
	for _, v := range f.afters {
		fmt.Printf("%d ~ ", v)
	}
	fmt.Println()
}

func (m *Machine) PrintMarksStack(f *Fiber) {
	fmt.Printf("MARKS:     ")
	if len(f.marks) <= 0 {
		fmt.Printf("<empty>")
	}
	for _, mark := range f.marks {
		fmt.Printf("(id:%d n:%d <", mark.markId, mark.nesting)
		for _, st := range mark.handlers {
			m.PrintValue(st)
			fmt.Printf(", ")
		}
		fmt.Printf("> -> aft: %d - vs: %d, st:%d afts:%d) ~ ", mark.afterComplete, mark.valuesMark, mark.storedMark, mark.aftersMark)
	}
	fmt.Println()
}

func (m *Machine) PrintValue(v Value) {
	switch v := v.(type) {
	case *Fiber:
		fmt.Printf("fiber(")
		fmt.Printf("id = %d, ", v.Id)
		fmt.Printf("I = %d, ", v.Instruction)
		if v.HandlerId == nil {
			fmt.Printf("H = nil")
		} else {
			fmt.Printf("H = %d", *v.HandlerId)
		}
		fmt.Printf(")")
	case Closure:
		if val, hasLabel := m.labels[v.CodeStart]; hasLabel {
			fmt.Printf("closure(%s", val)
		} else {
			fmt.Printf("closure(%d", v.CodeStart)
		}
		if len(v.Captured) > 0 {
			fmt.Printf(" <")
			for _, v := range v.Captured {
				m.PrintValue(v)
				fmt.Printf(", ")
			}
			fmt.Printf(">")
		}
		fmt.Printf(")")
	case Ref:
		fmt.Printf("ref(%d: ", v.Pointer)
		m.PrintValue(m.Heap[v.Pointer])
		fmt.Print(")")
	case Composite:
		fmt.Printf("cmp(%d", v.id)
		if len(v.elements) > 0 {
			fmt.Printf(": ")
			for _, v := range v.elements {
				m.PrintValue(v)
				fmt.Print(", ")
			}
		}
		fmt.Printf(")")
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
		fmt.Printf(")")
	default:
		fmt.Print(v)
	}
}
