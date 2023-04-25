package boolean

import (
	"fmt"

	"github.com/glossopoeia/boba/compiler/util"
	"github.com/rjNemo/underscore"
	"golang.org/x/exp/constraints"
	"golang.org/x/exp/maps"
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

func NewFlex[T constraints.Ordered](v T, dotted bool) Equation[T] {
	return BVar[T]{v, dotted, false}
}

func NewRigid[T constraints.Ordered](v T, dotted bool) Equation[T] {
	return BVar[T]{v, dotted, true}
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

// Create a new Boolean Not equation from the equation to be negated,
// applying some minor simplifications if possible.
func NewNot[T constraints.Ordered](neg Equation[T]) Equation[T] {
	switch n := neg.(type) {
	case BTrue[T]:
		return BFalse[T]{}
	case BFalse[T]:
		return BTrue[T]{}
	case BNot[T]:
		return n.Elem
	default:
		return BNot[T]{neg}
	}
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
	return NewNot(b.Elem.Substitute(subst))
}

type BAnd[T constraints.Ordered] struct {
	Left  Equation[T]
	Right Equation[T]
}

// Create a new Boolean And equation from two components, applying some minor simplifications
// if possible.
func NewAnd[T constraints.Ordered](left Equation[T], right Equation[T]) Equation[T] {
	switch left.(type) {
	case BTrue[T]:
		return right
	case BFalse[T]:
		return BFalse[T]{}
	default:
		switch right.(type) {
		case BTrue[T]:
			return left
		case BFalse[T]:
			return BFalse[T]{}
		default:
			return BAnd[T]{left, right}
		}
	}
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
	return NewAnd(b.Left.Substitute(subst), b.Right.Substitute(subst))
}

type BOr[T constraints.Ordered] struct {
	Left  Equation[T]
	Right Equation[T]
}

// Create a new Boolean Or equation from two components, applying some minor simplifications
// if possible.
func NewOr[T constraints.Ordered](left Equation[T], right Equation[T]) Equation[T] {
	switch left.(type) {
	case BTrue[T]:
		return BTrue[T]{}
	case BFalse[T]:
		return right
	default:
		switch right.(type) {
		case BTrue[T]:
			return BTrue[T]{}
		case BFalse[T]:
			return left
		default:
			return BOr[T]{left, right}
		}
	}
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
	return NewOr(b.Left.Substitute(subst), b.Right.Substitute(subst))
}

// Create a new Boolean Xor equation from two components, applying some minor simplifications
// if possible.
func NewXor[T constraints.Ordered](l Equation[T], r Equation[T]) Equation[T] {
	return NewOr(NewAnd(l, NewNot(r)), NewAnd(NewNot(l), r))
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

// Eliminate variables one by one by substituting them away  and builds up a
// resulting substitution. If the equation is satisfiable, the result is nil.
// This is because unification in Boolean rings is matching when the equation
// equals false.
func successiveVariableElimination[T constraints.Ordered](eqn Equation[T], vars []T) Substitution[T] {
	if len(vars) == 0 {
		if !Satisfiable(Minimize(eqn)) {
			return Substitution[T]{}
		} else {
			return nil
		}
	}

	v := vars[0]
	vFalse := eqn.Substitute(Substitution[T]{v: BFalse[T]{}})
	vTrue := eqn.Substitute(Substitution[T]{v: BTrue[T]{}})
	subst := successiveVariableElimination(NewAnd(vFalse, vTrue), vars[1:])
	if subst != nil {
		vSub := NewOr(vFalse.Substitute(subst), NewAnd(NewFlex(v, false), NewNot(vTrue.Substitute(subst))))
		return util.MergeMaps(Substitution[T]{v: vSub}, subst, func(l, r Equation[T]) Equation[T] { return l })
	}
	return nil
}

// Checks whether a given equation is satisfiable, i.e. whether there is a substitution
// of all variables to T or F that makes the equation T when evaluated.
func Satisfiable[T constraints.Ordered](eqn Equation[T]) bool {
	switch eqn.(type) {
	case BTrue[T]:
		return true
	case BFalse[T]:
		return false
	default:
		flexed := NewXor(eqn.Flexify(maps.Keys(FreeRigid(eqn))), Equation[T](BTrue[T]{}))
		return successiveVariableElimination(flexed, maps.Keys(FreeFlex(flexed))) != nil
	}
}

// Generate a most-general substitution that, when applied to both input equations,
// makes them equivalent boolean equations.
func Unify[T constraints.Ordered](l Equation[T], r Equation[T]) Substitution[T] {
	// turn it into one equation to perform successive variable elimination
	eqn := NewXor(l, r)
	// find whichever side has fewer free variables, and eliminate those variables first
	// to yield a smaller unifier. Sort to maintain determinism of resulting unifier
	lfree := maps.Keys(FreeFlex(l))
	slices.Sort(lfree)
	rfree := maps.Keys(FreeFlex(r))
	slices.Sort(rfree)
	var sveVars []T
	if len(lfree) <= len(rfree) {
		sveVars = append(lfree, underscore.Difference(rfree, lfree)...)
	} else {
		sveVars = append(rfree, underscore.Difference(lfree, rfree)...)
	}

	subst := successiveVariableElimination(eqn, sveVars)
	for k, v := range subst {
		subst[k] = Minimize(v)
	}
	return subst
}
