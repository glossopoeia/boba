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
	return f.frames[len(f.frames)-int(index)]
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
func (f *Fiber) FindFreeHandler(handleId int) (HandleFrame, uint) {
	for i := len(f.frames) - 1; i >= 0; i-- {
		frame := f.frames[i]
		switch frame.(type) {
		case HandleFrame:
			handle := frame.(HandleFrame)
			if handle.handleId == handleId && handle.nesting == 0 {
				return handle, uint(i)
			}
		default:
			continue
		}
	}
	panic("Could not find an unnested handle frame with the desired identifier.")
}
