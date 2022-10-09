package runtime

import "context"

type Marker struct {
	params        []Value
	afterComplete CodePointer
	markId        int
	nesting       uint
	afterClosure  Closure
	handlers      []Closure

	valuesMark int
	storedMark int
	aftersMark int
}

type Context struct {
	Ctx context.Context
}

type Fiber struct {
	Instruction CodePointer
	Cancelled   bool
	// The stack of values operated on directly by most instructions, such as add or multiply.
	values []Value
	// Used to save values and put them back on the value stack later by referring to their particular
	// index in the store stack.
	stored []Value
	// Used to save a location to jump back to after executing a particular block of instructions.
	afters []CodePointer
	// Used to mark a particular location in the stored and after stacks so they can be captured during
	// escape handler operations and replayed as continuations.
	marks   []Marker
	Context []Context
	caller  *Fiber
}

func NewFiber(caller *Fiber, ctxStack []Context) *Fiber {
	fiber := new(Fiber)
	fiber.Instruction = 0
	fiber.Cancelled = false
	fiber.values = make([]Value, 0)
	fiber.stored = make([]Value, 0)
	fiber.afters = make([]CodePointer, 0)
	fiber.marks = make([]Marker, 0)
	fiber.caller = caller
	fiber.Context = make([]Context, len(ctxStack))
	copy(fiber.Context, ctxStack)
	return fiber
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

func (f *Fiber) PushAfter(a uint) {
	f.afters = append(f.afters, a)
}

func (f *Fiber) PopAfter() uint {
	stackLen := len(f.afters)
	if stackLen <= 0 {
		panic("After-stack underflow detected.")
	}

	result := f.afters[stackLen-1]
	f.afters = f.afters[:stackLen-1]
	return result
}

func (f *Fiber) PushMarker(m Marker) {
	f.marks = append(f.marks, m)
}

func (f *Fiber) PopMarker() Marker {
	stackLen := len(f.marks)
	if stackLen <= 0 {
		panic("Marker-stack underflow detected.")
	}

	result := f.marks[stackLen-1]
	f.marks = f.marks[:stackLen-1]
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

func (f *Fiber) PushContext(ctx context.Context) {
	f.Context = append(f.Context, Context{ctx})
}

func (f *Fiber) PopContext() context.Context {
	stackLen := len(f.Context)
	if stackLen <= 0 {
		panic("Context-stack underflow detected.")
	}

	result := f.Context[stackLen-1]
	f.Context = f.Context[:stackLen-1]
	return result.Ctx
}

func (f *Fiber) LastCancelContext() Context {
	return f.Context[len(f.Context)-1]
}

// Generic function to create a call frame from a closure based on some data
// known about it. Can supply a sequences of values that will be spliced between the
// parameters and the captured values, but if this isn't needed, supply an empty slice
// for it. Modifies the fiber stack, and expects the parameters to be in
// correct order at the top of the stack.
func (fiber *Fiber) SetupClosureCallStored(closure Closure, markerParams []Value, cont *Continuation) {
	fiber.stored = append(fiber.stored, closure.captured...)
	fiber.stored = append(fiber.stored, markerParams...)

	fiber.stored = append(fiber.stored, fiber.values[uint(len(fiber.values))-closure.paramCount:]...)
	fiber.values = fiber.values[:uint(len(fiber.values))-closure.paramCount]
	if cont != nil {
		fiber.stored = append(fiber.stored, *cont)
	}
}

func (fiber *Fiber) RestoreSaved(marker Marker, cont Continuation, after CodePointer) {
	// we basically copy the marker, but update the parameters passed along through the
	// handling context and forget the 'return location'
	updated := Marker{
		make([]Value, len(marker.params)),
		after,
		marker.markId,
		marker.nesting,
		marker.afterClosure,
		marker.handlers,
		marker.valuesMark,
		len(fiber.stored),
		len(fiber.afters),
	}

	// take any handle parameters off the stack
	for i := 0; i < len(marker.params); i++ {
		updated.params[i] = fiber.PopOneValue()
	}

	//savedValues := fiber.values
	//fiber.values = make([]Value, 0)
	fiber.values = append(fiber.values, cont.savedValues...)
	//fiber.values = append(fiber.values, savedValues...)

	// saved stored values and returns just go on top of the existing elements
	fiber.PushMarker(updated)
	fiber.stored = append(fiber.stored, cont.savedStored...)
	fiber.afters = append(fiber.afters, cont.savedAfters...)
}

// Walk the frame stack backwards looking for a handle frame with the given
// handle id that is 'unnested', i.e. with a nesting level of 0. Injecting
// increases the nesting levels of the nearest handle frames with a giContext
// handle id, while ejecting decreases the nesting level. This dual
// functionality allows some actions to be handled by handlers 'containing'
// inner handlers that would otherwise have handled the action. This function
// drives the actual effect of the nesting by continuing to walk down handle
// frames even if a handle frame with the requested id is found if it is
// 'nested', i.e. with a nesting level greater than 0.
func (f *Fiber) FindFreeMarker(markId int) (Marker, uint, int) {
	for i := len(f.marks) - 1; i >= 0; i-- {
		marker := f.marks[i]
		if marker.markId == markId && marker.nesting == 0 {
			return marker, uint(len(f.marks) - i), i
		}
	}
	panic("Could not find an unnested handle frame with the desired identifier.")
}
