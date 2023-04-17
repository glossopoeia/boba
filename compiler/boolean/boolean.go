package boolean

import (
	"fmt"

	"golang.org/x/exp/constraints"
)

// Represents a Boolean equation with variables and the standard Boolean constants.
// How these constants and variables are interpreted is up to the consumer of this
// data type. For Boba, though, we include dotted variables, which are generally
// substituted with a sequence that is converted to nested disjunctions. There is
// also a distinction between rigid and flexible variables: only flexible variables
// are considered 'free', and thus only they will be included in the unifier during
// unification. This enables us to do 'boolean matching' by setting one side of the
// equation to rigid, and the other flexible.
type Equation[T constraints.Ordered] interface {
	fmt.Stringer
	// Helper method to construct the free set of variables efficiently
	// for each equation variant.
	freeAcc(map[T]int)
}

type BTrue struct{}

type BFalse struct{}

type BVar[T constraints.Ordered] struct {
	Name   T
	Dotted bool
	Rigid  bool
}

type BNot[T constraints.Ordered] struct {
	Elem Equation[T]
}

type BAnd[T constraints.Ordered] struct {
	Left  Equation[T]
	Right Equation[T]
}

type BOr[T constraints.Ordered] struct {
	Left  Equation[T]
	Right Equation[T]
}
