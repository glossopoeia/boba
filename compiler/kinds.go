package compiler

import "fmt"

// Every kind in the Boba type system has a sort. The sort is the
// top the of the type abstraction hierarchy, but is not used for
// well-formedness or soundness so much as controlling unification
// during type inference.
type Sort int

const (
	// Kinds of syntactic sort unify syntactically, which will be the most familiar
	// to implementers and students of HM type inference.
	SortSyntactic Sort = iota + 1
	// Kinds of Boolean sort unify using Boolean unification, which is unitary but
	// has complex equational rules that yield interesting type system capabilities.
	SortBoolean
	// Kinds of Abelian sort unify using Abelian unification, which is unitary but
	// has extra equational rules that enable useful type system capabilities.
	SortAbelian
	// Kinds of Row sort unify using scoped Row unification, which is unitary but
	// allows the order of elements in the type row to shift without changing the
	// meaning of the type.
	SortRow
	// Kinds of Sequence sort unify using Sequence unification, which is unitary
	// under controlled circumstances (i.e. all sequence variables are the last
	// element of the sequence, and only appear in that position in any given
	// sequence). Elements in the sequence do not change order, unlike for row
	// unification, but sequence variables can be expanded in a more powerful way
	// than row variables, enabling variable-arity tuples and other neat features.
	SortSequence
)

func (s Sort) String() string {
	switch s {
	case SortSyntactic:
		return "syn"
	case SortBoolean:
		return "bool"
	case SortAbelian:
		return "abel"
	case SortRow:
		return "row"
	case SortSequence:
		return "seq"
	default:
		panic("Invalid sort encountered.")
	}
}

// The kind system of Boba is similar to that of many functional languages,
// featuring base kinds, kind variables, and an arrow constructor. However,
// there are also 'row' and 'sequence' kinds in the Boba kind system, which
// are useful to distinguish in the type system and help guide unification
// during type inference. Kinds are used to determine whether a type is well-
// formed, and kind inference is used to help improve the generality of data
// type definitions. Boba supports polymorphic kind inference. Kinds
// themselves always unify syntactically.
type Kind[T int | string] interface {
	fmt.Stringer
	// Helper method to construct the free set of variables efficiently
	// for each kind variant.
	freeAcc(map[T]int)
}

// The number of occurrences of each distinct variable in the kind.
func KindFree[T int | string](k Kind[T]) map[T]int {
	occ := make(map[T]int)
	k.freeAcc(occ)
	return occ
}

// Given an arrow kind `(k1 -> k2)`, return whether the argument kind `k3` is
// equal to `k1`. If the arrow kind is not actually an arrow, returns false.
func CanApplyKind[T int | string](arr Kind[T], arg Kind[T]) bool {
	switch arrk := any(arr).(type) {
	case KindArrow[T]:
		return arrk.Input == arg
	default:
		return false
	}
}

// Contains extra information about a failure to apply a kind during type checking.
type KindApplyError[T int | string] struct {
	Arrow    Kind[T]
	Argument Kind[T]
}

func (k KindApplyError[T]) Error() string {
	switch any(k.Arrow).(type) {
	case KindArrow[T]:
		return fmt.Sprintf("kinds: could not apply %s to %s", k.Arrow.String(), k.Argument.String())
	default:
		return fmt.Sprintf("kinds: tried to apply %s but is not an arrow kind", k.Arrow.String())
	}
}

/// Given an arrow kind `(k1 -> k2)`, if the argument kind `k3` is equal to `k1`, return `k2`.
/// If `k1` doesn't equal `k3`, or if arr is not actually an arrow kind, return a KindApplyError.
func ApplyKind[T int | string](arr Kind[T], arg Kind[T]) (Kind[T], error) {
	switch arrk := any(arr).(type) {
	case KindArrow[T]:
		if arrk.Input == arg {
			return arrk.Output, nil
		} else {
			return nil, KindApplyError[T]{arr, arg}
		}
	default:
		return nil, KindApplyError[T]{arr, arg}
	}
}

// Represents a kind variable. Each variable has a name and unification
// sort attached to it. When a variable maps to a kind in a substitution,
// the sort of the variable and the mapped kind must match.
type KindVar[T int | string] struct {
	Name T
	Sort Sort
}

// Create a new kind variable with syntactic unify sort.
func SynKVar[T int | string](name T) Kind[T] {
	return KindVar[T]{Name: name, Sort: SortSyntactic}
}

// Create a new kind variable with Boolean unify sort.
func BoolKVar[T int | string](name T) Kind[T] {
	return KindVar[T]{Name: name, Sort: SortBoolean}
}

func (k KindVar[T]) String() string {
	return fmt.Sprint(k.Name)
}

func (k KindVar[T]) freeAcc(acc map[T]int) {
	if occ, ok := acc[k.Name]; ok {
		acc[k.Name] = occ + 1
	} else {
		acc[k.Name] = 1
	}
}

// A base kind is either a pre-defined or user-defined kind constructor.
// These are treated as constants, and so unlike kind variables only unify
// with themselves. Primitive kinds are defined in the Boba standard library
// the same as any other user-defined kind, which is why they do not have
// built-in struct variants here.
type KindBase[T int | string] struct {
	Name T
	Sort Sort
}

/// Create a new base kind with the given name and sort.
func KBase[T int | string](name T, sort Sort) Kind[T] {
	return KindBase[T]{Name: name, Sort: sort}
}

func (k KindBase[T]) String() string {
	return fmt.Sprint(k.Name)
}

func (k KindBase[T]) freeAcc(acc map[T]int) {}

// A row kind is the specific kind of a row type, and contains the
// element kind of the row type as a subcomponent. Row kinds are used
// to drive unification, and always have sort SortRow.
type KindRow[T int | string] struct {
	Elem Kind[T]
}

// Create a new row kind with the given element kind.
func KRow[T int | string](k Kind[T]) Kind[T] {
	return KindRow[T]{k}
}

func (k KindRow[T]) String() string {
	return fmt.Sprintf("<%s>", k.Elem.String())
}

func (k KindRow[T]) freeAcc(acc map[T]int) {
	k.Elem.freeAcc(acc)
}

// A sequence kind is the specific kind of a sequence type, and contains
// the element kind of the sequence type as a subcomponent. While rows
// will generally only have a base or variable kind as the subcomponent,
// sequence kinds may often have nested (lower rank) sequence kinds as
// their subcomponent.
type KindSeq[T int | string] struct {
	Elem Kind[T]
}

// Create a new sequence kind with the given element kind.
func KSeq[T int | string](k Kind[T]) Kind[T] {
	return KindSeq[T]{k}
}

func (k KindSeq[T]) String() string {
	return fmt.Sprintf("[%s]", k.Elem.String())
}

func (k KindSeq[T]) freeAcc(acc map[T]int) {
	k.Elem.freeAcc(acc)
}

// Sequence types may be nested, especially in substitutions, and this
// nesting has a rank, defined to be number of sequence kinds directly
// nested proceeding down the sequence hierarchy until the first non-sequence
// kind is reached.
func (k KindSeq[T]) Rank() int {
	switch kt := any(k.Elem).(type) {
	case KindSeq[T]:
		return kt.Rank() + 1
	default:
		return 0
	}
}

// The familiar higher-kind constructor. Creates a kind representing a type
// constructor that takes an argument. The input kind is for the argument,
// the output kind specifies the constructor result.
type KindArrow[T int | string] struct {
	Input  Kind[T]
	Output Kind[T]
}

// Create an arrow kind with the given input and output kinds.
func KArrow[T int | string](inp Kind[T], out Kind[T]) Kind[T] {
	return KindArrow[T]{Input: inp, Output: out}
}

func (k KindArrow[T]) String() string {
	switch any(k.Input).(type) {
	case KindArrow[T]:
		return fmt.Sprintf("(%s) -> %s", k.Input, k.Output)
	default:
		return fmt.Sprintf("%s -> %s", k.Input, k.Output)
	}
}

func (k KindArrow[T]) freeAcc(acc map[T]int) {
	k.Input.freeAcc(acc)
	k.Output.freeAcc(acc)
}
