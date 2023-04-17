package compiler

import (
	"golang.org/x/exp/maps"
)

// Represents an Abelian equation composed of constant values and variables,
// each of which can have a signed integer exponent. The implementation uses
// dictionaries as a form of signed multiset, where an element in the set can
// have more than one occurence (represented by a positive exponent) or even
// negative occurences (represented by a negative exponent). If an element has
// exactly zero occurences, it is removed from the dictionary for efficiency.
type AbelianEquation[K comparable, V comparable] struct {
	// The variables of the equation and their associated exponents.
	Variables map[K]int
	// The constants of the equation and their associated exponents.
	Constants map[V]int
}

// A substitution on abelian equations, where K is the type of the variables
// in the equation and V the type of the constants.
type AbelianSubstitution[K comparable, V comparable] map[K]AbelianEquation[K, V]

// Create the identity Abelian equation, with no variables and no constants.
func AbelianIdentity[K comparable, V comparable]() AbelianEquation[K, V] {
	return AbelianEquation[K, V]{make(map[K]int), make(map[V]int)}
}

// Create a single variable Abelian equation.
func AbelianVariable[K comparable, V comparable](varName K) AbelianEquation[K, V] {
	return AbelianEquation[K, V]{map[K]int{varName: 1}, map[V]int{}}
}

// True if the equation has no variables and no constants.
func (eqn AbelianEquation[K, V]) IsIdentity() bool {
	return len(eqn.Variables) == 0 && len(eqn.Constants) == 0
}

// True if the equation has no variables.
func (eqn AbelianEquation[K, V]) IsConstant() bool {
	return len(eqn.Variables) == 0
}

// Get the variables of the equation without their associated exponents.
func (eqn AbelianEquation[K, V]) Free() []K {
	return maps.Keys(eqn.Variables)
}

// Get the exponent of the given variable name within this equation.
// Returns 0 if the variable is not present.
func (eqn AbelianEquation[K, V]) ExponentOf(v K) int {
	if e, ok := eqn.Variables[v]; ok {
		return e
	}
	return 0
}

// Negate all the exponents in the equation.
func (eqn AbelianEquation[K, V]) Invert() AbelianEquation[K, V] {
	inverted := AbelianEquation[K, V]{maps.Clone(eqn.Variables), maps.Clone(eqn.Constants)}
	for k, v := range inverted.Variables {
		inverted.Variables[k] = -v
	}
	for k, v := range inverted.Constants {
		inverted.Constants[k] = -v
	}
	return inverted
}

// Combine two Abelian equations via summing. Values that appear in both equations
// have their exponents multiplied.
func (eqn AbelianEquation[K, V]) Add(other AbelianEquation[K, V]) AbelianEquation[K, V] {
	mergeAdd := func(l, r int) int { return l + r }
	expNotZero := func(v int) bool { return v != 0 }
	vars := mergeMaps(eqn.Variables, other.Variables, mergeAdd)
	consts := mergeMaps(eqn.Constants, other.Constants, mergeAdd)
	vars = mapFilterValue(vars, expNotZero)
	consts = mapFilterValue(consts, expNotZero)
	return AbelianEquation[K, V]{vars, consts}
}

// Removes the given equation from this Abelian unit equation. Equivalent to `eqn.Add(other.Invert())`.
func (eqn AbelianEquation[K, V]) Subtract(other AbelianEquation[K, V]) AbelianEquation[K, V] {
	return eqn.Add(other.Invert())
}

// Generate a substitution that, when applied to eqn, makes it equal to other with
// respect to the equational rules for Abelian systems. The approach employed is
// that of solving linear diophantine equations. If there is no way to match the
// equations, the resulting substitution is nil.
func (eqn AbelianEquation[K, V]) Match(fresh Fresh[K], other AbelianEquation[K, V]) AbelianSubstitution[K, V] {

	if eqn.IsConstant() && other.IsConstant() {
		if maps.Equal(eqn.Constants, other.Constants) {
			return AbelianSubstitution[K, V]{}
		}
		return nil
	}
	if eqn.IsConstant() {
		return nil
	}

	// put all constants on the 'constant' side of the equation, so that the matching side only has variables
	right := other.Subtract(AbelianEquation[K, V]{map[K]int{}, eqn.Constants})

	// convert a few of the variable and constants maps into slices,
	// for multiple deterministic indexed traversals
	ordEqnVars := make([]K, len(eqn.Variables))
	ordEqnExps := make([]int, len(eqn.Variables))
	ordRightVars := make([]K, len(right.Variables))
	ordRightVarExps := make([]int, len(right.Variables))
	ordRightConsts := make([]V, len(right.Constants))
	ordRightConstExps := make([]int, len(right.Constants))
	for i, k := range maps.Keys(eqn.Variables) {
		ordEqnVars[i] = k
		ordEqnExps[i] = eqn.Variables[k]
	}
	for i, k := range maps.Keys(right.Variables) {
		ordRightVars[i] = k
		ordRightVarExps[i] = right.Variables[k]
	}
	for i, c := range maps.Keys(right.Constants) {
		ordRightConsts[i] = c
		ordRightConstExps[i] = right.Constants[c]
	}

	// convert into a linear diophantine equation for solving
	linear := LinearEquation{ordEqnExps, append(ordRightVarExps, ordRightConstExps...)}

	// if a solution exists, convert the linear equation substitution into an Abelian substitution
	if solution := linear.Solution(); solution != nil {
		// linear solution can have more variables that original equation
		varCount := len(maps.Values(solution)[0].Coefficients)
		fresh := fresh.NextN(varCount)

		// convert the linear substitution variable indexes into named variables
		varSubst := AbelianSubstitution[K, V]{}
		for i, k := range ordEqnVars {
			// convert the solution equation into an Abelian equation
			if sub, ok := solution[i]; ok {
				// convert flex variables
				flexVarExps := map[K]int{}
				for fi, fv := range fresh {
					flexVarExps[fv] = sub.Coefficients[fi]
				}
				// convert constant variables
				constVarExps := map[K]int{}
				for ci, cv := range ordRightVars {
					constVarExps[cv] = sub.Constants[ci]
				}
				// convert constants
				constExps := map[V]int{}
				for ci, cc := range ordRightConsts {
					constExps[cc] = sub.Constants[ci+len(right.Variables)]
				}

				//combine converted subequations into a single equation
				combined := AbelianEquation[K, V]{flexVarExps, map[V]int{}}.Add(
					AbelianEquation[K, V]{constVarExps, map[V]int{}},
				).Add(
					AbelianEquation[K, V]{map[K]int{}, constExps},
				)
				varSubst[k] = combined
			} else {
				varSubst[k] = AbelianVariable[K, V](fresh[i])
			}
		}
		return varSubst
	}
	return nil
}

// Generate a most general unifier that, when applied to both eqn and other, makes the resulting
// Abelian equations equal with respect to the equational rules for Abelian systems.
// The approach employed is that of solving linear diophantine equations. If there is no way
// to unify the equations, the resulting substitution is nil.
func (eqn AbelianEquation[K, V]) Unify(fresh Fresh[K], other AbelianEquation[K, V]) AbelianSubstitution[K, V] {
	return eqn.Add(other.Invert()).Match(fresh, AbelianIdentity[K, V]())
}
