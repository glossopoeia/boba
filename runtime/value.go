package runtime

import (
	"context"
	"sync"
)

type ResumeLimit = int

// This enum provides a way for compiler writers to specify that some closures-as-handlers have
// certain assumptions guaranteed that allow more efficient operation. For instance, RESUME_NONE
// will prevent a handler closure from capturing the continuation, since it is never resumed anyway,
// saving a potentially large allocation and copy. RESUME_ONCE_TAIL treats a handler closure call
// just like any other closure call. The most general option, but the least efficient, is RESUME_MANY,
// which can be thought of as the default for handler closures. The default for all closures is
// RESUME_MANY, even those which are never used as handlers, because continuation saving is only done
// during the ESCAPE instruction and so RESUME_MANY is never acted upon for the majority of closures.
const (
	ResumeMany ResumeLimit = iota
	ResumeOnce
	ResumeOnceTail
	ResumeNever
)

type Value interface{}

type Closure struct {
	CodeStart   CodePointer
	paramCount  uint
	resumeLimit ResumeLimit
	captured    []Value
}

type Continuation struct {
	resume      CodePointer
	caller      *Fiber
	savedValues []Value
	savedStored []Value
	savedAfters []CodePointer
	savedMarks  []Marker
}

type NativeVal struct {
	val interface{}
}

type ValueArray struct {
	elements []Value
}

type ByteArray struct {
	elements []byte
}

type Ref struct {
	Pointer HeapKey
}

type CompositeId = int

type Composite struct {
	id       CompositeId
	elements []Value
}

type Variant struct {
	label int
	value Value
}

func (variant Variant) Clone() Variant {
	return Variant{variant.label, variant.value}
}

type Nursery struct {
	Waiter *sync.WaitGroup
}

type CancelToken struct {
	Cancel context.CancelFunc
}
