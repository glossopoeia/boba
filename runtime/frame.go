package runtime

type Frame interface {
	Slots() []Value
}

type VariableFrame struct {
	slots []Value
}

func (f VariableFrame) Slots() []Value {
	return f.slots
}

type CallFrame struct {
	*VariableFrame
	afterLocation CodePointer
}

type HandleFrame struct {
	*CallFrame
	handleId     int
	nesting      uint
	afterClosure *Closure
	handlers     []*Closure
}
