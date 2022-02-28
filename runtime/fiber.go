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

func (f *Fiber) PeekFrameAt(index uint) Frame {
	return f.frames[len(f.frames)-int(index)]
}
