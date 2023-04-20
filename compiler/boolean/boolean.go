package boolean

import (
	"fmt"

	"golang.org/x/exp/constraints"
	"golang.org/x/exp/slices"
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
	freeAcc(map[T]Occurence, bool)
	// Make a subset of named rigids in the equation into flex variables.
	Flexify([]T) Equation[T]
	// Make a subset of flex variables into rigid variables in the equation.
	Rigidify([]T) Equation[T]
	// Substitute all occurences of the variables present in the substitution
	// with their assigned equation in the target Boolean equation.
	Substitute(Substitution[T]) Equation[T]
}

// Represents how many times a variable occurs in an equation when computing the
// set of free variables, and whether the variable occurred dotted or not.
type Occurence struct {
	Count  int
	Dotted bool
}

// A substitution on boolean equations, where T is the type of the variable names
// in the equation. Each T is mapped to a boolean sub-equation that will replace
// the variable in the equation and be simplified when subsitution is complete.
type Substitution[T constraints.Ordered] map[T]Equation[T]

type MinTermRow struct {
	Name map[int]bool
	Row  []int
}

const (
	MinTrue  int = 1
	MinFalse int = 0
	MinDash  int = 2
)

type BTrue[T constraints.Ordered] struct{}

func (b BTrue[T]) String() string {
	return "T"
}

func (b BTrue[T]) freeAcc(acc map[T]Occurence, rigid bool) {}

func (b BTrue[T]) Flexify(subset []T) Equation[T] { return b }

func (b BTrue[T]) Rigidify(subset []T) Equation[T] { return b }

func (b BTrue[T]) Substitute(subst Substitution[T]) Equation[T] { return b }

type BFalse[T constraints.Ordered] struct{}

func (b BFalse[T]) String() string {
	return "F"
}

func (b BFalse[T]) freeAcc(acc map[T]Occurence, rigid bool) {}

func (b BFalse[T]) Flexify(subset []T) Equation[T] { return b }

func (b BFalse[T]) Rigidify(subset []T) Equation[T] { return b }

func (b BFalse[T]) Substitute(subst Substitution[T]) Equation[T] { return b }

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

func (v BVar[T]) freeAcc(acc map[T]Occurence, rigid bool) {
	if v.Rigid == rigid {
		if occ, ok := acc[v.Name]; ok {
			acc[v.Name] = Occurence{occ.Count + 1, v.Dotted || occ.Dotted}
		} else {
			acc[v.Name] = Occurence{1, v.Dotted}
		}
	}
}

func (b BVar[T]) Flexify(subset []T) Equation[T] {
	if b.Rigid && slices.Contains(subset, b.Name) {
		return BVar[T]{b.Name, b.Dotted, false}
	}
	return b
}

func (b BVar[T]) Rigidify(subset []T) Equation[T] {
	if !b.Rigid && slices.Contains(subset, b.Name) {
		return BVar[T]{b.Name, b.Dotted, true}
	}
	return b
}

func (b BVar[T]) Substitute(subst Substitution[T]) Equation[T] {
	if !b.Rigid {
		if sub, ok := subst[b.Name]; ok {
			return sub
		}
	}
	return b
}

type BNot[T constraints.Ordered] struct {
	Elem Equation[T]
}

func (n BNot[T]) String() string {
	return fmt.Sprintf("!(%s)", n.Elem)
}

func (n BNot[T]) freeAcc(acc map[T]Occurence, rigid bool) {
	n.Elem.freeAcc(acc, rigid)
}

func (b BNot[T]) Flexify(subset []T) Equation[T] { return BNot[T]{b.Elem.Flexify(subset)} }

func (b BNot[T]) Rigidify(subset []T) Equation[T] { return BNot[T]{b.Elem.Rigidify(subset)} }

func (b BNot[T]) Substitute(subst Substitution[T]) Equation[T] {
	return BNot[T]{b.Elem.Substitute(subst)}
}

type BAnd[T constraints.Ordered] struct {
	Left  Equation[T]
	Right Equation[T]
}

func (a BAnd[T]) String() string {
	return fmt.Sprintf("(%s && %s)", a.Left, a.Right)
}

func (a BAnd[T]) freeAcc(acc map[T]Occurence, rigid bool) {
	a.Left.freeAcc(acc, rigid)
	a.Right.freeAcc(acc, rigid)
}

func (b BAnd[T]) Flexify(subset []T) Equation[T] {
	return BAnd[T]{b.Left.Flexify(subset), b.Right.Flexify(subset)}
}

func (b BAnd[T]) Rigidify(subset []T) Equation[T] {
	return BAnd[T]{b.Left.Rigidify(subset), b.Right.Rigidify(subset)}
}

func (b BAnd[T]) Substitute(subst Substitution[T]) Equation[T] {
	return BAnd[T]{b.Left.Substitute(subst), b.Right.Substitute(subst)}
}

type BOr[T constraints.Ordered] struct {
	Left  Equation[T]
	Right Equation[T]
}

func (o BOr[T]) String() string {
	return fmt.Sprintf("(%s || %s)", o.Left, o.Right)
}

func (a BOr[T]) freeAcc(acc map[T]Occurence, rigid bool) {
	a.Left.freeAcc(acc, rigid)
	a.Right.freeAcc(acc, rigid)
}

func (b BOr[T]) Flexify(subset []T) Equation[T] {
	return BOr[T]{b.Left.Flexify(subset), b.Right.Flexify(subset)}
}

func (b BOr[T]) Rigidify(subset []T) Equation[T] {
	return BOr[T]{b.Left.Rigidify(subset), b.Right.Rigidify(subset)}
}

func (b BOr[T]) Substitute(subst Substitution[T]) Equation[T] {
	return BOr[T]{b.Left.Substitute(subst), b.Right.Substitute(subst)}
}

// The number of occurrences of each distinct flexible variable in the equation.
func FreeFlex[T constraints.Ordered](eqn Equation[T]) map[T]Occurence {
	occ := make(map[T]Occurence)
	eqn.freeAcc(occ, false)
	return occ
}

// The number of occurrences of each distinct rigid variable in the equation.
func FreeRigid[T constraints.Ordered](eqn Equation[T]) map[T]Occurence {
	occ := make(map[T]Occurence)
	eqn.freeAcc(occ, true)
	return occ
}
