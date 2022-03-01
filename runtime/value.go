package runtime

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
	codeStart   CodePointer
	paramCount  uint
	resumeLimit ResumeLimit
	captured    []Value
}

type Continuation struct {
	resume      CodePointer
	paramCount  uint
	savedValues []Value
	savedFrames []Frame
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
	pointer HeapKey
}

type CompositeId = int

type Composite struct {
	id      CompositeId
	elemnts []Value
}

type Label = int

type Field struct {
	label Label
	value Value
}

type Record struct {
	fields []Field
}

type Variant struct {
	label   Label
	value   Value
	nesting uint
}
