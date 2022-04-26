package runtime

type Fiber struct {
	instruction CodePointer
	values      []Value
	frames      []Frame
	roots       []Value
	caller      *Fiber
}

func (f *Fiber) PushValue(v Value) {
	f.values = append(f.values, v)
}

func (f *Fiber) PopOneValue() Value {
	stackLen := len(f.values)
	if stackLen <= 0 {
		panic("Stack underflow detected.")
	}

	result := f.values[stackLen-1]
	f.values = f.values[:stackLen-1]
	return result
}

func (f *Fiber) Clear() {
	f.values = make([]Value, 0)
}

func (f *Fiber) Gather() {
	tpl := f.values
	f.values = make([]Value, 0)
	f.PushValue(tpl)
}

func (f *Fiber) Spread() {
	tpl := f.PopOneValue().([]Value)
	f.values = append(tpl, f.values...)
}

func (f *Fiber) PopTwoValues() (fst Value, snd Value) {
	stackLen := len(f.values)
	if stackLen <= 1 {
		panic("Stack underflow detected.")
	}

	r1 := f.values[stackLen-1]
	r2 := f.values[stackLen-2]
	f.values = f.values[:stackLen-2]
	return r1, r2
}

func (f *Fiber) PeekOneValue() Value {
	stackLen := len(f.values)
	if stackLen <= 0 {
		panic("Stack underflow detected.")
	}
	return f.values[:stackLen-1]
}

func (f *Fiber) PushFrame(fr Frame) {
	f.frames = append(f.frames, fr)
}

func (f *Fiber) PopFrame() Frame {
	stackLen := len(f.frames)
	if stackLen <= 0 {
		panic("Stack underflow detected.")
	}

	result := f.frames[stackLen-1]
	f.frames = f.frames[:stackLen-1]
	return result
}

func (f *Fiber) DropFrames(dropCount uint) {
	f.frames = f.frames[:len(f.frames)-int(dropCount)]
}

func (f *Fiber) PeekFrameAt(index uint) Frame {
	return f.frames[len(f.frames)-1-int(index)]
}

// Generic function to create a call frame from a closure based on some data
// known about it. Can supply a var frame that will be spliced between the
// parameters and the captured values, but if this isn't needed, supply `nil`
// for it. Modifies the fiber stack, and expects the parameters to be in
// correct order at the top of the stack.
func (fiber *Fiber) SetupClosureCall(closure Closure, vars *VariableFrame, cont *Continuation, after uint) CallFrame {
	frameSlots := make([]Value, 0)

	if cont != nil {
		frameSlots = append(frameSlots, *cont)
	}

	for i := 0; i < int(closure.paramCount); i++ {
		frameSlots = append(frameSlots, fiber.PopOneValue())
	}

	if vars != nil {
		frameSlots = append(frameSlots, vars.slots...)
	}

	frameSlots = append(frameSlots, closure.captured...)
	return CallFrame{VariableFrame{frameSlots}, after}
}

func (fiber *Fiber) RestoreSaved(frame HandleFrame, cont Continuation, after CodePointer) {
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

// Walk the frame stack backwards looking for a handle frame with the given
// handle id that is 'unnested', i.e. with a nesting level of 0. Injecting
// increases the nesting levels of the nearest handle frames with a given
// handle id, while ejecting decreases the nesting level. This dual
// functionality allows some actions to be handled by handlers 'containing'
// inner handlers that would otherwise have handled the action. This function
// drives the actual effect of the nesting by continuing to walk down handle
// frames even if a handle frame with the requested id is found if it is
// 'nested', i.e. with a nesting level greater than 0.
func (f *Fiber) FindFreeHandler(handleId int) (HandleFrame, uint, int) {
	for i := len(f.frames) - 1; i >= 0; i-- {
		frame := f.frames[i]
		switch frame := frame.(type) {
		case HandleFrame:
			if frame.handleId == handleId && frame.nesting == 0 {
				return frame, uint(len(f.frames) - i), i
			}
		default:
			continue
		}
	}
	panic("Could not find an unnested handle frame with the desired identifier.")
}

// Create and push a new variable frame containing `varCount` values from the top
// of the stack. The values are ordered top-most at the least index.
func (f *Fiber) StoreVars(varCount int) {
	valsLen := len(f.values)
	if valsLen < varCount {
		panic("STORE: Not enough values to store in frame")
	}
	frame := VariableFrame{make([]Value, varCount)}
	copy(frame.slots, f.values[valsLen-varCount:])
	// reverse frame slots array to get the top-most stack value at the zero index
	for i := len(frame.slots)/2 - 1; i >= 0; i-- {
		opp := len(frame.slots) - 1 - i
		frame.slots[i], frame.slots[opp] = frame.slots[opp], frame.slots[i]
	}
	f.values = f.values[:valsLen-varCount]
	f.PushFrame(frame)
}
