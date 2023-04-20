package boolean

import (
	"fmt"

	"golang.org/x/exp/constraints"
)

// Compute the truth table for the given equation, returning a two dimensional list of the
// form [[T, T, ..., T],...,[F, F,..., T]] where the last element in each sublist is the
// truth value of the equation for that row. Returns an error if the equation contains any
// rigids, which cannot be substituted for.
func truthTable[T constraints.Ordered](eqn Equation[T], free []T) ([][]int, error) {
	if len(free) == 0 {
		switch eqn.(type) {
		case BTrue[T]:
			return [][]int{{MinTrue}}, nil
		case BFalse[T]:
			return [][]int{{MinFalse}}, nil
		default:
			return nil, fmt.Errorf("boolean: found non-value Boolean in truth table: %s", eqn)
		}
	}

	vTrue, trueErr := truthTable(eqn.Substitute(Substitution[T]{free[0]: BTrue[T]{}}), free[1:])
	if trueErr != nil {
		return nil, trueErr
	}
	vFalse, falseErr := truthTable(eqn.Substitute(Substitution[T]{free[0]: BFalse[T]{}}), free[1:])
	if falseErr != nil {
		return nil, falseErr
	}
	for row := range vTrue {
		vTrue[row] = append([]int{MinTrue}, vTrue[row]...)
		vFalse[row] = append([]int{MinFalse}, vFalse[row]...)
	}
	return append(vTrue, vFalse...), nil
}

func truthRowToInt(truth []int) int {
	res := 0
	for i, e := range truth {
		res += e << i
	}
	return res
}

/*func primeImplicants(minTerms []MinTermRow) []MinTermRow {
	grouped :=
}

// Minimize a Boolean equation with variables using the Quine-McCluskey method.
func Minimize[T constraints.Ordered](eqn Equation[T]) error {
	// find any rigids and flexify them so they simplify, rigidify them after minimization complete
	rigids := FreeRigid(eqn)
	flex := eqn.Flexify(maps.Keys(rigids))

	free := FreeFlex(flex)

	truth, err := truthTable(flex, maps.Keys(free))
	if err != nil {
		return err
	}

	// minTerms are elements of the truth table where the result is T.
	// It is convenient to not include the truth value element, so we remove
	// it from each row.
	minTermRows := [][]int{}
	for _, t := range truth {
		if t[len(minTermRows)-1] == MinTrue {
			minTermRows = append(minTermRows, t[:len(minTermRows)-1])
		}
	}

	// give each minTerm a unique (but meaningful) name to efficiently refer to it later
	namedMinTerms := make([]MinTermRow, len(minTermRows))
	for i, r := range minTermRows {
		namedMinTerms[i] = MinTermRow{map[int]bool{truthRowToInt(r): true}, r}
	}

	primes := primeImplicants(namedMinTerms)
	essentials, covered, remaining, uncovered := essentialImplicants(primes, namedMinTerms)

	var finalImplicants []MinTermRow
	if len(uncovered) != 0 {
		covering := petricks(remaining, uncovered)
		finalImplicants = append(essentials, covering...)
	} else {
		finalImplicants = essentials
	}

	// convert the final implicants back into equation form

	return minified.Rigidify(rigids)
}*/
