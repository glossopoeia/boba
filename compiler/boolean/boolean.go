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
	freeAcc(map[T]int, bool)
	// Make a subset of named rigids in the equation into flex variables.
	Flexify([]T) Equation[T]
	// Make a subset of flex variables into rigid variables in the equation.
	Rigidify([]T) Equation[T]
}

// A substitution on boolean equations, where T is the type of the variable names
// in the equation. Each T is mapped to a boolean sub-equation that will replace
// the variable in the equation and be simplified when subsitution is complete.
type Substitution[T constraints.Ordered] map[T]Equation[T]

type MinTermRow struct {
	Name map[int]bool
	Row  []int
}

type BTrue[T constraints.Ordered] struct{}

func (b BTrue[T]) String() string {
	return "T"
}

func (b BTrue[T]) freeAcc(acc map[T]int, rigid bool) {}

type BFalse[T constraints.Ordered] struct{}

func (b BFalse[T]) String() string {
	return "F"
}

func (b BFalse[T]) freeAcc(acc map[T]int, rigid bool) {}

type BVar[T constraints.Ordered] struct {
	Name   T
	Dotted bool
	Rigid  bool
}

func (v BVar[T]) String() string {
	if v.Dotted {
		if v.Rigid {
			return fmt.Sprintf("%v*...", v.Name)
		} else {
			return fmt.Sprintf("%v...", v.Name)
		}
	} else {
		if v.Rigid {
			return fmt.Sprintf("%v*", v.Name)
		} else {
			return fmt.Sprintf("%v", v.Name)
		}
	}
}

func (v BVar[T]) freeAcc(acc map[T]int, rigid bool) {
	if v.Rigid == rigid {
		if occ, ok := acc[v.Name]; ok {
			acc[v.Name] = occ + 1
		} else {
			acc[v.Name] = 1
		}
	}
}

type BNot[T constraints.Ordered] struct {
	Elem Equation[T]
}

func (n BNot[T]) String() string {
	return fmt.Sprintf("!(%s)", n.Elem)
}

func (n BNot[T]) freeAcc(acc map[T]int, rigid bool) {
	n.Elem.freeAcc(acc, rigid)
}

type BAnd[T constraints.Ordered] struct {
	Left  Equation[T]
	Right Equation[T]
}

func (a BAnd[T]) String() string {
	return fmt.Sprintf("(%s && %s)", a.Left, a.Right)
}

func (a BAnd[T]) freeAcc(acc map[T]int, rigid bool) {
	a.Left.freeAcc(acc, rigid)
	a.Right.freeAcc(acc, rigid)
}

type BOr[T constraints.Ordered] struct {
	Left  Equation[T]
	Right Equation[T]
}

func (o BOr[T]) String() string {
	return fmt.Sprintf("(%s || %s)", o.Left, o.Right)
}

func (a BOr[T]) freeAcc(acc map[T]int, rigid bool) {
	a.Left.freeAcc(acc, rigid)
	a.Right.freeAcc(acc, rigid)
}

// The number of occurrences of each distinct flexible variable in the equation.
func FreeFlex[T constraints.Ordered](eqn Equation[T]) map[T]int {
	occ := make(map[T]int)
	eqn.freeAcc(occ, false)
	return occ
}

// The number of occurrences of each distinct rigid variable in the equation.
func FreeRigid[T constraints.Ordered](eqn Equation[T]) map[T]int {
	occ := make(map[T]int)
	eqn.freeAcc(occ, true)
	return occ
}
