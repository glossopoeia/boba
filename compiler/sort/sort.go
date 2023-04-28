package sort

// Every kind in the Boba type system has a sort. The sort is the
// top the of the type abstraction hierarchy, but is not used for
// well-formedness or soundness so much as controlling unification
// during type inference.
type Sort int

const (
	// Kinds of syntactic sort unify syntactically, which will be the most familiar
	// to implementers and students of HM type inference.
	Syntactic Sort = iota + 1
	// Kinds of Boolean sort unify using Boolean unification, which is unitary but
	// has complex equational rules that yield interesting type system capabilities.
	Boolean
	// Kinds of Abelian sort unify using Abelian unification, which is unitary but
	// has extra equational rules that enable useful type system capabilities.
	Abelian
	// Kinds of Row sort unify using scoped Row unification, which is unitary but
	// allows the order of elements in the type row to shift without changing the
	// meaning of the type.
	Row
	// Kinds of Sequence sort unify using Sequence unification, which is unitary
	// under controlled circumstances (i.e. all sequence variables are the last
	// element of the sequence, and only appear in that position in any given
	// sequence). Elements in the sequence do not change order, unlike for row
	// unification, but sequence variables can be expanded in a more powerful way
	// than row variables, enabling variable-arity tuples and other neat features.
	Sequence
)

func (s Sort) String() string {
	switch s {
	case Syntactic:
		return "syn"
	case Boolean:
		return "bool"
	case Abelian:
		return "abel"
	case Row:
		return "row"
	case Sequence:
		return "seq"
	default:
		panic("Invalid sort encountered.")
	}
}
