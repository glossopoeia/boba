package kind

import (
	"fmt"

	"github.com/glossopoeia/boba/compiler/sort"
)

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
func CanApply[T int | string](arr Kind[T], arg Kind[T]) bool {
	switch arrk := any(arr).(type) {
	case Arrow[T]:
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
	case Arrow[T]:
		return fmt.Sprintf("kinds: could not apply %s to %s", k.Arrow.String(), k.Argument.String())
	default:
		return fmt.Sprintf("kinds: tried to apply %s but is not an arrow kind", k.Arrow.String())
	}
}

// / Given an arrow kind `(k1 -> k2)`, if the argument kind `k3` is equal to `k1`, return `k2`.
// / If `k1` doesn't equal `k3`, or if arr is not actually an arrow kind, return a KindApplyError.
func ApplyKind[T int | string](arr Kind[T], arg Kind[T]) (Kind[T], error) {
	switch arrk := any(arr).(type) {
	case Arrow[T]:
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
type Var[T int | string] struct {
	Name T
	Sort sort.Sort
}

// Create a new kind variable with syntactic unify sort.
func SynVar[T int | string](name T) Kind[T] {
	return Var[T]{Name: name, Sort: sort.Syntactic}
}

// Create a new kind variable with Boolean unify sort.
func BoolVar[T int | string](name T) Kind[T] {
	return Var[T]{Name: name, Sort: sort.Boolean}
}

func (k Var[T]) String() string {
	return fmt.Sprint(k.Name)
}

func (k Var[T]) freeAcc(acc map[T]int) {
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
type Base[T int | string] struct {
	Name string
	Sort sort.Sort
}

// / Create a new base kind with the given name and sort.
func NewBase[T int | string](name string, sort sort.Sort) Kind[T] {
	return Base[T]{Name: name, Sort: sort}
}

func (k Base[T]) String() string {
	return fmt.Sprint(k.Name)
}

func (k Base[T]) freeAcc(acc map[T]int) {}

// A row kind is the specific kind of a row type, and contains the
// element kind of the row type as a subcomponent. Row kinds are used
// to drive unification, and always have sort SortRow.
type Row[T int | string] struct {
	Elem Kind[T]
}

// Create a new row kind with the given element kind.
func NewRow[T int | string](k Kind[T]) Kind[T] {
	return Row[T]{k}
}

func (k Row[T]) String() string {
	return fmt.Sprintf("<%s>", k.Elem.String())
}

func (k Row[T]) freeAcc(acc map[T]int) {
	k.Elem.freeAcc(acc)
}

// A sequence kind is the specific kind of a sequence type, and contains
// the element kind of the sequence type as a subcomponent. While rows
// will generally only have a base or variable kind as the subcomponent,
// sequence kinds may often have nested (lower rank) sequence kinds as
// their subcomponent.
type Seq[T int | string] struct {
	Elem Kind[T]
}

// Create a new sequence kind with the given element kind.
func NewSeq[T int | string](k Kind[T]) Kind[T] {
	return Seq[T]{k}
}

func (k Seq[T]) String() string {
	return fmt.Sprintf("[%s]", k.Elem.String())
}

func (k Seq[T]) freeAcc(acc map[T]int) {
	k.Elem.freeAcc(acc)
}

// Sequence types may be nested, especially in substitutions, and this
// nesting has a rank, defined to be number of sequence kinds directly
// nested proceeding down the sequence hierarchy until the first non-sequence
// kind is reached.
func (k Seq[T]) Rank() int {
	switch kt := any(k.Elem).(type) {
	case Seq[T]:
		return kt.Rank() + 1
	default:
		return 0
	}
}

// The familiar higher-kind constructor. Creates a kind representing a type
// constructor that takes an argument. The input kind is for the argument,
// the output kind specifies the constructor result.
type Arrow[T int | string] struct {
	Input  Kind[T]
	Output Kind[T]
}

// Create an arrow kind with the given input and output kinds.
func NewArrow[T int | string](inp Kind[T], out Kind[T]) Kind[T] {
	return Arrow[T]{Input: inp, Output: out}
}

func (k Arrow[T]) String() string {
	switch any(k.Input).(type) {
	case Arrow[T]:
		return fmt.Sprintf("(%s) -> %s", k.Input, k.Output)
	default:
		return fmt.Sprintf("%s -> %s", k.Input, k.Output)
	}
}

func (k Arrow[T]) freeAcc(acc map[T]int) {
	k.Input.freeAcc(acc)
	k.Output.freeAcc(acc)
}

func NewInt[T int | string]() Kind[T] {
	return NewBase[T]("Int", sort.Syntactic)
}

func NewData[T int | string]() Kind[T] {
	return NewBase[T]("Data", sort.Syntactic)
}

func NewShare[T int | string]() Kind[T] {
	return NewBase[T]("Share", sort.Boolean)
}

func NewValue[T int | string]() Kind[T] {
	return NewBase[T]("Value", sort.Syntactic)
}

func NewConstraint[T int | string]() Kind[T] {
	return NewBase[T]("Constraint", sort.Syntactic)
}

func NewEffect[T int | string]() Kind[T] {
	return NewBase[T]("Effect", sort.Syntactic)
}

func NewField[T int | string]() Kind[T] {
	return NewBase[T]("Field", sort.Syntactic)
}

func NewPermission[T int | string]() Kind[T] {
	return NewBase[T]("Permission", sort.Syntactic)
}

func NewTotality[T int | string]() Kind[T] {
	return NewBase[T]("Totality", sort.Boolean)
}

func NewFixed[T int | string]() Kind[T] {
	return NewBase[T]("Fixed", sort.Abelian)
}

func NewMeasure[T int | string]() Kind[T] {
	return NewBase[T]("Data", sort.Abelian)
}

func NewTrust[T int | string]() Kind[T] {
	return NewBase[T]("Trust", sort.Boolean)
}

func NewClear[T int | string]() Kind[T] {
	return NewBase[T]("Clear", sort.Boolean)
}

func NewHeap[T int | string]() Kind[T] {
	return NewBase[T]("Heap", sort.Syntactic)
}
