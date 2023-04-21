package boolean

import (
	"fmt"

	"github.com/glossopoeia/boba/compiler/util"
	"github.com/rjNemo/underscore"
	"golang.org/x/exp/constraints"
	"golang.org/x/exp/maps"
	"golang.org/x/exp/slices"

	mapset "github.com/deckarep/golang-set/v2"
)

type MinTermRow struct {
	Name mapset.Set[int]
	Row  []int
}

const (
	MinTrue  int = 1
	MinFalse int = 0
	MinDash  int = 2
)

func generateComparedRow(left []int, right []int) ([]int, bool) {
	difference := false
	tooMany := false
	row := []int{}
	for i := 0; i < len(left); i++ {
		// are they different at the same index?
		if left[i] != right[i] {
			// already seen a difference? if so, too many
			if difference {
				tooMany = true
			} else {
				difference = true
				// just one difference so far, mark it with a dash
				row = append(row, MinDash)
			}
		} else {
			// same value at same index, propagate into the generated row
			row = append(row, left[i])
		}
	}
	if difference && !tooMany {
		return row, true
	} else {
		return []int{}, false
	}
}

func (m MinTermRow) CompareAgainst(others []MinTermRow) ([]MinTermRow, []MinTermRow) {
	implicants := []MinTermRow{}
	matched := []MinTermRow{}
	for _, o := range others {
		if genRow, ok := generateComparedRow(m.Row, o.Row); ok {
			implicants = append(implicants, MinTermRow{m.Name.Union(o.Name), genRow})
			matched = append(matched, o)
		}
	}
	return implicants, matched
}

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

func minTermKindCount(kind int, minTerm MinTermRow) int {
	res := 0
	for _, i := range minTerm.Row {
		if i == kind {
			res += 1
		}
	}
	return res
}

func minTermRowEq(l MinTermRow, r MinTermRow) bool {
	return slices.Equal(l.Row, r.Row)
}

func primeImplicants(minTerms []MinTermRow) []MinTermRow {
	byTrue := func(minTerm MinTermRow) int { return minTermKindCount(MinTrue, minTerm) }
	// group min terms by the number of True elements in their row
	grouped := underscore.GroupBy(minTerms, byTrue)
	// keys don't matter, just need them stored such that lower true count rows
	// are compared with the next higher true count rows, which is why we sort
	tCounts := maps.Keys(grouped)
	slices.Sort(tCounts)
	remaining := make([][]MinTermRow, len(tCounts))
	for i, c := range tCounts {
		remaining[i] = grouped[c]
	}

	// iteratively deduce the set of prime implicants from the min terms
	// each step introduces a new number of possible 'dashes' that appear
	// in the minTerms as we cross out common elements
	steps := 1
	primeImplicants := []MinTermRow{}
	for {
		checkedImplicants := []MinTermRow{}
		nextRemaining := []MinTermRow{}

		for i := 0; i < len(remaining)-1; i++ {
			for _, minTerm := range remaining[i] {
				implicants, matched := minTerm.CompareAgainst(remaining[i+1])
				if len(matched) > 0 {
					checkedImplicants = append([]MinTermRow{minTerm}, append(checkedImplicants, matched...)...)
				}
				nextRemaining = append(implicants, nextRemaining...)
			}
		}

		checkedImplicants = util.UniqueCmp(checkedImplicants, minTermRowEq)
		nextRemaining = util.UniqueCmp(checkedImplicants, minTermRowEq)

		// all the unchecked rows are prime implicants
		primes := []MinTermRow{}
		for _, r := range remaining {
			for _, g := range r {
				if !underscore.Any(checkedImplicants, func(c MinTermRow) bool { return c.Name.Equal(g.Name) }) {
					primes = append(primes, g)
				}
			}
		}
		primeImplicants = append(primes, primeImplicants...)

		// no implicants had a check put next to them? we're done
		if len(checkedImplicants) == 0 {
			break
		}

		// otherwise, group the next remaining minTerm set same as we did before
		// and continue the loop
		grouped = underscore.GroupBy(nextRemaining, byTrue)
		// keys don't matter, just need them stored such that lower true count rows
		// are compared with the next higher true count rows, which is why we sort
		tCounts = maps.Keys(grouped)
		slices.Sort(tCounts)
		remaining = make([][]MinTermRow, len(tCounts))
		for i, c := range tCounts {
			remaining[i] = grouped[c]
		}

		steps += 1
	}

	return primeImplicants
}

func essentialImplicants(primes []MinTermRow, minTerms []MinTermRow) (
	[]MinTermRow, mapset.Set[int], []MinTermRow, []MinTermRow) {

	essentials := []MinTermRow{}
	for _, m := range minTerms {
		checks := underscore.Filter(primes, func(p MinTermRow) bool { return m.Name.IsSubset(p.Name) })
		if len(checks) == 1 {
			essentials = append(essentials, checks[0])
		}
	}
	covered := underscore.Map(essentials, func(e MinTermRow) mapset.Set[int] { return e.Name })
	coverSet := underscore.Reduce(covered, mapset.Set[int].Union, mapset.NewSet[int]())
	// determine which prime implicants and minterms are remaining to be investigated
	remaining := underscore.Filter(primes,
		func(p MinTermRow) bool {
			return !underscore.Any(essentials,
				func(e MinTermRow) bool { return p.Name.Equal(e.Name) })
		})
	uncovered := underscore.Filter(minTerms,
		func(m MinTermRow) bool { return !m.Name.IsSubset(coverSet) })
	return essentials, coverSet, remaining, uncovered
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
		namedMinTerms[i] = MinTermRow{mapset.NewSet(truthRowToInt(r)), r}
	}

	primes := primeImplicants(namedMinTerms)
	essentials, _, remaining, uncovered := essentialImplicants(primes, namedMinTerms)

	var finalImplicants []MinTermRow
	if len(uncovered) != 0 {
		covering := petricks(remaining, uncovered)
		finalImplicants = append(essentials, covering...)
	} else {
		finalImplicants = essentials
	}

	// convert the final implicants back into equation form

	return minified.Rigidify(rigids)
}
