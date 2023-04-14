package compiler

import (
	"math"
)

// Represents a linear diophantine equation.
type LinearEquation struct {
	Coefficients []int
	Constants    []int
}

// A substitution on linear diophantine equations, where the integer keys
// are an index into the coefficient list, representing the variable that
// the coefficient is applied to.
type LinearSubstitution map[int]LinearEquation

// Optimized and does not have problems with integer overflow.
func absInt(n int) int {
	y := n >> 63
	return (n ^ y) - y
}

func divFloor(n int, m int) int {
	q := n / m
	r := n % m
	if (r > 0 && m < 0) || (r < 0 && m > 0) {
		return q - 1
	}
	return q
}

func modulo(n int, m int) int {
	r := n % m
	if (r > 0 && m < 0) || (r < 0 && m > 0) {
		return r + m
	}
	return r
}

// Find the non-zero coefficient closest to zero in the list. Return the
// index at which the smallest non-zero element was found, and the element
// itself in that order.
func smallest(coeffs []int) (int, int) {
	small := math.MaxInt
	ind := -1
	for i, c := range coeffs {
		if c != 0 && absInt(c) < absInt(small) {
			small = c
			ind = i
		}
	}
	return ind, small
}

// Negate all the integers in a list.
func negate(ns []int) []int {
	nr := make([]int, len(ns))
	for i, n := range ns {
		nr[i] = -n
	}
	return nr
}

// Replace the integer at index i in a list with 0.
func zeroAt(index int, ns []int) []int {
	nr := make([]int, len(ns))
	copy(nr, ns)
	nr[index] = 0
	return nr
}

// Check if every number in a list is divisible by a given divisor.
func divisible(divisor int, ns []int) bool {
	res := true
	for _, n := range ns {
		res = res && modulo(n, divisor) == 0
	}
	return res
}

// Divide every number in a list by the given divisor.
func divide(divisor int, ns []int) []int {
	nr := make([]int, len(ns))
	for i, n := range ns {
		nr[i] = divFloor(n, divisor)
	}
	return nr
}

func addMul(n int, xs []int, ys []int) []int {
	resLen := len(xs)
	if len(ys) > resLen {
		resLen = len(ys)
	}
	nr := make([]int, resLen)

	for i := 0; i < resLen; i++ {
		if i >= len(ys) {
			nr[i] = xs[i]
		} else if i >= len(xs) {
			nr[i] = n * ys[i]
		} else {
			nr[i] = xs[i] + n*ys[i]
		}
	}
	return nr
}

// Eliminate the variable at index i if it exists in Equation eqn. Returns a copy of eqn
// modified such that the variable i has been removed.
func elim(i int, orig LinearEquation, eqn LinearEquation) LinearEquation {
	if i >= len(eqn.Coefficients) || eqn.Coefficients[i] == 0 {
		res := LinearEquation{make([]int, len(eqn.Coefficients)), make([]int, len(eqn.Constants))}
		copy(res.Coefficients, eqn.Coefficients)
		copy(res.Constants, eqn.Constants)
		return res
	} else {
		return LinearEquation{
			addMul(eqn.Coefficients[i], zeroAt(i, eqn.Coefficients), orig.Coefficients),
			addMul(eqn.Coefficients[i], eqn.Constants, orig.Constants),
		}
	}
}

// Eliminate a variable from the substitution. If the variable is in the original problem,
// add it to the substitution and remove the variable from the existing values in the
// substitution.
func eliminate(v int, smallestInd int, orig LinearEquation, subst LinearSubstitution) LinearSubstitution {
	res := make(map[int]LinearEquation)
	for k, v := range subst {
		res[k] = elim(smallestInd, orig, v)
	}
	if smallestInd < v {
		res[smallestInd] = orig
	}
	return res
}

// Find a solution for the linear diophantine equation, if one exists.
// If one exists, return it, otherwise return nil.
func (eqn LinearEquation) Solution() LinearSubstitution {
	if len(eqn.Coefficients) <= 0 {
		return nil
	}

	working := eqn
	originalEqnVarCount := len(eqn.Coefficients)
	subst := make(map[int]LinearEquation)
	for {
		smInd, smVal := smallest(working.Coefficients)

		// make sure the coefficient closest to zero is positive
		if smVal < 0 {
			working = LinearEquation{negate(working.Coefficients), negate(working.Constants)}
			continue
		}

		// no coefficients left is an internal error
		if smVal == 0 {
			panic("linear: no coefficients left in loop")
		}

		// solution is found, eliminate the variable
		if smVal == 1 {
			el := LinearEquation{negate(zeroAt(smInd, working.Coefficients)), working.Constants}
			return eliminate(originalEqnVarCount, smInd, el, subst)
		}

		// if the coefficients are divisble by the smallest non-zero coefficient,
		// we know there's either a solution or not immediately
		if divisible(smVal, working.Coefficients) {
			// if the constants are also divisible by the smallest, we have a solution
			if divisible(smVal, working.Constants) {
				divCoeffs := divide(smVal, working.Coefficients)
				divConsts := divide(smVal, working.Constants)
				el := LinearEquation{negate(zeroAt(smInd, divCoeffs)), divConsts}
				return eliminate(originalEqnVarCount, smInd, el, subst)
			} else {
				// otherwise, we know there's no solution
				return nil
			}
		}

		// otherwise we introduce a new variable and solve
		coeffs := divide(smVal, zeroAt(smInd, working.Coefficients))
		el := LinearEquation{append(negate(coeffs), 1), []int{}}

		subst = eliminate(originalEqnVarCount, smInd, el, subst)

		nextCoeffs := make([]int, len(working.Coefficients))
		for i, m := range working.Coefficients {
			nextCoeffs[i] = modulo(m, smVal)
		}
		working = LinearEquation{
			append(nextCoeffs, smVal),
			working.Constants,
		}
	}
}
