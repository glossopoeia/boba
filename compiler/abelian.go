package compiler

import "golang.org/x/exp/maps"

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
