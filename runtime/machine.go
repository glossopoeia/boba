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
			fiber.stored = append(fiber.stored, fiber.values[len(fiber.values)-varCount:]...)
			fiber.values = fiber.values[:len(fiber.values)-varCount]
		case FIND:
			varInd := uint(fiber.ReadUInt32(m))
			fiber.PushValue(fiber.stored[uint(len(fiber.stored))-varInd-1])
		case OVERWRITE:
			varInd := uint(fiber.ReadUInt32(m))
			fiber.stored[uint(len(fiber.stored))-varInd-1] = fiber.PopOneValue()
		case FORGET:
			varCount := int(fiber.ReadUInt8(m))
			fiber.stored = fiber.stored[:len(fiber.stored)-varCount]

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
			fiber.SetupClosureCallStored(closure, []Value{}, nil)
			// push return location and jump to new location
			fiber.afters = append(fiber.afters, fiber.Instruction)
			fiber.Instruction = closure.CodeStart
		case TAILCALL_CLOSURE:
			closure := fiber.PopOneValue().(Closure)
			fiber.SetupClosureCallStored(closure, []Value{}, nil)
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
			paramCount := fiber.ReadUInt8(m)
			closedCount := fiber.ReadUInt16(m)

			closure := Closure{CodePointer(codeStart), uint(paramCount), ResumeMany, make([]Value, closedCount)}
			for i := 0; i < int(closedCount); i++ {
				// the distance the variable value is from the top of the variable stack
				varInd := fiber.ReadUInt32(m)
				varVal := fiber.stored[len(fiber.stored)-1-int(varInd)]
				closure.captured[i] = varVal
			}
			fiber.PushValue(closure)
		case RECURSIVE:
			codeStart := fiber.ReadUInt32(m)
			paramCount := fiber.ReadUInt8(m)
			closedCount := fiber.ReadUInt16(m)

			closure := Closure{CodePointer(codeStart), uint(paramCount), ResumeMany, make([]Value, closedCount+1)}
			closure.captured[0] = closure
			for i := 0; i < int(closedCount); i++ {
				// the distance the variable value is from the top of the variable stack
				varInd := fiber.ReadUInt32(m)
				varVal := fiber.stored[len(fiber.stored)-1-int(varInd)]
				closure.captured[i+1] = varVal
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
				newC := Closure{oldC.CodeStart, oldC.paramCount, oldC.resumeLimit, make([]Value, len(oldC.captured)+mutualCount)}
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

			handlers := make([]Closure, handlerCount+1)
			for i := uint(0); i < handlerCount; i++ {
				handlers[i+1] = fiber.PopOneValue().(Closure)
			}
			afterClosure := fiber.PopOneValue().(Closure)
			handlers[0] = afterClosure

			params := make([]Value, paramCount)
			for i := uint(0); i < paramCount; i++ {
				params[i] = fiber.PopOneValue()
			}

			marker := Marker{
				params,
				// TODO: this int() conversion is a bit bad
				uint(int(fiber.Instruction) + after),
				handleId,
				0,
				afterClosure,
				handlers,
				len(fiber.values),
				len(fiber.stored),
				len(fiber.afters),
				make([]Value, 0),
				make([]uint, 0),
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
			fiber.PopMarker()
			/*if fiber.caller != nil {
				marker := fiber.PeekMarker()
				fiber.caller.values = append(fiber.caller.values, fiber.values[marker.valuesMark:]...)
				fiber = fiber.caller
			} else {
				fiber.PopMarker()
			}*/

			/*marker := fiber.PopMarker()
			fiber.SetupClosureCallStored(marker.afterClosure, marker.params, nil)
			// push return location and jump to new location
			fiber.afters = append(fiber.afters, marker.afterComplete)
			fiber.Instruction = marker.afterClosure.CodeStart*/
		case ESCAPE:
			handleId := int(fiber.ReadInt32(m))
			handlerInd := fiber.ReadUInt8(m)
			marker, _, capturedStartIndex := fiber.FindFreeMarker(handleId)
			handler := marker.handlers[handlerInd]

			cloned := fiber.CloneFiber(m, fiber)
			cloned.HandlerId = new(int)
			*cloned.HandlerId = handleId
			cloned.Instruction = handler.CodeStart
			cloned.stored = cloned.stored[:marker.storedMark]
			cloned.afters = cloned.afters[:marker.aftersMark]
			cloned.marks = cloned.marks[:capturedStartIndex]

			// put captured variables in environment
			cloned.stored = append(cloned.stored, handler.captured...)
			cloned.stored = append(cloned.stored, marker.params...)

			// put closure parameters variables in environment, and modify the original fiber to
			// 'pass them in' to the cloned fiber
			cloned.stored = append(cloned.stored, cloned.values[uint(len(cloned.values))-handler.paramCount:]...)
			fiber.values = fiber.values[:uint(len(fiber.values))-handler.paramCount]

			// reset values further down to where the mark was after consuming them
			cloned.values = make([]Value, 0) //cloned.values[marker.valuesMark:]

			// make the current fiber available as a 'continuation' to the cloned one
			cloned.stored = append(cloned.stored, fiber)

			fiber = cloned

			/*if handler.resumeLimit == ResumeNever {
				// handler promises to never resume, so no need to capture the continuation
				fiber.SetupClosureCallStored(handler, marker.params, &Continuation{})
				// just drop the stored and returns that would have been captured
				fiber.values = make([]Value, 0)
				fiber.stored = fiber.stored[:marker.storedMark]
				fiber.afters = fiber.afters[:marker.aftersMark]
				fiber.marks = fiber.marks[:capturedStartIndex]
				fiber.afters = append(fiber.afters, marker.afterComplete)
				marker.storedMark = len(fiber.stored)
				marker.aftersMark = len(fiber.afters)
			} else if handler.resumeLimit == ResumeOnceTail {
				// handler promises to only resume at the end of it's execution, and does not thread parameters through the effect
				fiber.SetupClosureCallStored(handler, marker.params, &Continuation{})
				fiber.stored = fiber.stored[:marker.storedMark]
				fiber.afters = append(fiber.afters, fiber.Instruction)
			} else {
				contParamCount := len(marker.params)
				cont := Continuation{
					fiber.Instruction,
					uint(contParamCount),
					make([]Value, len(fiber.values)-marker.valuesMark-int(handler.paramCount)),
					make([]Value, len(fiber.stored)-marker.storedMark),
					make([]uint, len(fiber.afters)-marker.aftersMark),
					make([]Marker, capturedMarkCount)}

				copy(cont.savedValues, fiber.values[marker.valuesMark:uint(len(fiber.values))-handler.paramCount])
				copy(cont.savedStored, fiber.stored[marker.storedMark:])
				copy(cont.savedAfters, fiber.afters[marker.aftersMark:])
				copy(cont.savedMarks, fiber.marks[capturedStartIndex:])

				fiber.stored = fiber.stored[:marker.storedMark]
				fiber.afters = fiber.afters[:marker.aftersMark]
				fiber.marks = fiber.marks[:capturedStartIndex]
				fiber.afters = append(fiber.afters, marker.afterComplete)
				marker.storedMark = len(fiber.stored)
				marker.aftersMark = len(fiber.afters)

				fiber.SetupClosureCallStored(handler, marker.params, &cont)
				fiber.values = fiber.values[:marker.valuesMark]
			}

			fiber.Instruction = handler.CodeStart*/
		case CALL_CONTINUATION:
			orig := fiber.PopOneValue().(*Fiber)
			clonedResume := orig.CloneFiber(m, fiber)

			clonedResume.values = append(clonedResume.values, fiber.values...)

			originalMarker, _, markerInd := clonedResume.FindFreeMarker(*fiber.HandlerId)
			clonedResume.marks[markerInd].afterComplete = fiber.Instruction
			for i := 0; i < len(originalMarker.params); i++ {
				clonedResume.marks[markerInd].params[i] = clonedResume.PopOneValue()
			}

			fiber.values = make([]Value, 0)

			fiber = clonedResume
			/*cont := fiber.PopOneValue().(Continuation)
			marker := cont.savedMarks[0]
			marker.storedSave = make([]Value, len(fiber.stored)-marker.storedMark)
			copy(marker.storedSave, fiber.stored[marker.storedMark:])
			marker.aftersSave = make([]uint, len(fiber.afters)-marker.aftersMark)
			copy(marker.aftersSave, fiber.afters[marker.aftersMark:])
			fiber.RestoreSaved(marker, cont, fiber.Instruction)
			fiber.Instruction = cont.resume*/
		case TAILCALL_CONTINUATION:
			// TODO: handling faked continuation here for now
			caller := fiber.PopOneValue().(*Fiber)
			caller.values = append(caller.values, fiber.values...)
			fiber = caller
			/*cont := fiber.PopOneValue().(Continuation)
			marker := cont.savedMarks[0]
			tailAfter := fiber.PopAfter()
			fiber.RestoreSaved(marker, cont, tailAfter)
			fiber.Instruction = cont.resume*/
		case RESTORE:
			// walk back up the call stack to find the nearest fiber with a similar marker
			// or the original calling fiber
			caller := fiber.caller
			if fiber.HandlerId == nil {
				panic(fiber.HandlerId)
			}
			for caller.caller != nil {
				caller = caller.caller
				if caller.HandlerId != nil && *caller.HandlerId == *fiber.HandlerId {
					break
				}
			}

			if caller.HandlerId == nil || *caller.HandlerId != *fiber.HandlerId {
				caller.Instruction = caller.PeekMarker().afterComplete
			}

			caller.values = append(caller.values, fiber.values...)
			fiber = caller
			//marker := fiber.PeekMarker()
			//fiber.stored = append(fiber.stored, marker.storedSave...)
			//fiber.afters = append(fiber.afters, marker.aftersSave...)

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
	if len(f.stored) <= 0 {
		fmt.Printf("<empty>")
	}
	for _, v := range f.stored {
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
		for _, par := range mark.params {
			m.PrintValue(par)
			fmt.Printf(", ")
		}
		fmt.Printf("> <")
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
			fmt.Printf("closure(%s %d", val, v.paramCount)
		} else {
			fmt.Printf("closure(%d %d", v.CodeStart, v.paramCount)
		}
		if len(v.captured) > 0 {
			fmt.Printf(" <")
			for _, v := range v.captured {
				m.PrintValue(v)
				fmt.Printf(", ")
			}
			fmt.Printf(">")
		}
		fmt.Printf(")")
	case Continuation:
		fmt.Printf("cont(%d -> %d <", v.paramCount, v.resume)
		for _, v := range v.savedStored {
			m.PrintValue(v)
			fmt.Printf(",")
		}
		fmt.Printf("> <")
		for _, f := range v.savedAfters {
			fmt.Printf("%d,", f)
		}
		fmt.Printf("> <")
		for i := range v.savedMarks {
			fmt.Printf("m(%d),", i)
		}
		fmt.Printf(">)")
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
