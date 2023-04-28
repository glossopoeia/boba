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
	// Truth rows for implicants may contain a DASH '-' during reduction to
	// the set of prime implicants, which is used to track where overlaps occur
	// during reduction iteration steps.
	MinDash int = 2
)

// Given two lists of (maybe dashed) Boolean values, checks whether they differ zipwise
// by one element. If they do, this returns an object indicating that the rows differed
// by one, as well as the compared row with the difference replaced by a dash. If they
// differ by more or less than one, return an object indicating as such with no result row.
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

// Compares `row` against the rows in `others` to determine which differ by
// one elements. Returns an object containing those rows in `others` which
// differed from `row` by only one element, alongisde those same rows with
// the differing element replaced by a dash (the generated implicant).
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

func termToSum[T constraints.Ordered](minTerm MinTermRow, freeOrd []T, free map[T]Occurence) Equation[T] {
	sum := Equation[T](BTrue[T]{})
	for i, r := range minTerm.Row {
		switch r {
		case MinTrue:
			sum = NewAnd(sum, NewFlex(freeOrd[i], free[freeOrd[i]].Dotted))
		case MinFalse:
			sum = NewAnd(sum, NewNot(NewFlex(freeOrd[i], free[freeOrd[i]].Dotted)))
		}
	}
	return sum
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

// Given a list of True and False values, converts the list to a number as if the
// list was a bitwise representation of the number.
func truthRowToInt(truth []int) int {
	res := 0
	for i, e := range truth {
		res += e << i
	}
	return res
}

// Given a row entry from a truth table, returns the number of elements
// in the row that are one of MinTrue, MinFalse, or MinDash.
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

// Given a set of named minTerms for a Boolean equation, generates the set
// of implicants that cannot be 'covered' by a 'more general' implicant, i.e.
// the set of prime implicants. Note that these prime implicants are not
// necessarily essential; some of them may overlap with each other with respect
// to the original equation, but none can be further reduced according to the
// given set of minTerms.
//
// The process here is iterative, checking off elements that reduce, accumulating
// those that do not, and repeating on the set of new reduced elements until no
// further reductions can take place.
//
// Returned implicants will be sorted such that the implicant that covers the most
// minTerms will be first.
func primeImplicants(minTerms []MinTermRow) []MinTermRow {
	byTrue := func(minTerm MinTermRow) int { return minTermKindCount(MinTrue, minTerm) }
	// Group the minTerms by the number of T elements each row contains.
	// We will compare rows with no Ts against rows with one T, rows with
	// one T against rows with two Ts, and so on...
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
		nextRemaining = util.UniqueCmp(nextRemaining, minTermRowEq)

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
	}

	return primeImplicants
}

// Given a set of prime implicants, and a set of minTerms that they collectively cover,
// returns the implicants which are 'essential'. An essential implicant is one which covers
// one of the minTerms and is the only implicant to cover that minTerm.
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

// Given a set of prime implicants and a set of minTerms, constructs
// a Boolean equation of the form ((b11+b12+b13+...)(b21+b22+b23+...)...(bn1+bn2+bn3+...))
// such that each sum b[i] contains the primes that cover minTerm[i]. Each b[i][j] is the name
// of the prime implicant, not the named row object representing the prime implicant itself,
// to make comparison easy during expansion. The names will be translated back into named
// implicant objects in the final step of Petricks.
func productOfSums(primes []MinTermRow, minTerms []MinTermRow) [][]mapset.Set[int] {
	res := [][]mapset.Set[int]{}
	for _, m := range minTerms {
		outer := []mapset.Set[int]{}
		for _, p := range primes {
			if m.Name.IsSubset(p.Name) {
				outer = append(outer, p.Name)
			}
		}
		res = append(res, outer)
	}
	return res
}

// Converts a product of sums (represented in list of lists of terms form) into an equivalent sum
// of products, applying some reduction laws to minify the result sum. Returns the new sum of
// products as a list of lists of terms.
func productOfSumsToSumOfProducts[E comparable](product [][]E) [][]E {
	sums := [][]E{product[0]}
	for _, term := range product[1:] {
		updatedSums := [][]E{}
		for _, t := range term {
			for _, s := range sums {
				if underscore.Contains(s, t) {
					updatedSums = append([][]E{s}, updatedSums...)
				} else {
					updatedSums = append([][]E{append([]E{t}, s...)}, updatedSums...)
				}
			}
		}
	}
	return reduceByAbsorption(sums)
}

// Given a sum of products (represented as a list of lists of terms) removes redundant products
// by applying the absorption laws (X+XY) = X. The result is still a sum of products.
func reduceByAbsorption[E comparable](sums [][]E) [][]E {
	reduced := [][]E{}
	for len(sums) > 0 {
		product := sums[0]
		sums = sums[1:]
		sumSubset := underscore.Any(sums, func(s []E) bool { return productIsSubset(s, product) })
		redSubset := underscore.Any(reduced, func(r []E) bool { return productIsSubset(r, product) })
		if sumSubset || redSubset {
			continue
		}
		reduced = append(reduced, product)
	}
	return reduced
}

// Returns whether a product of Boolean terms is a subset of another Boolean product.
func productIsSubset[E comparable](test []E, cmp []E) bool {
	return underscore.All(test, func(prime E) bool { return underscore.Contains(cmp, prime) })
}

// Given a set of prime implicants and minTerms where each minTerm is covered by
// at least two implicants, Petrick's method constructs a minimum sum-of-product
// term that covers all the given minTerms. The smallest term of this sum-of-product
// is returned as the minimal set of covering implicants.
func petricks(primes []MinTermRow, minTerms []MinTermRow) []MinTermRow {
	products := productOfSums(primes, minTerms)
	sum := productOfSumsToSumOfProducts(products)
	slices.SortStableFunc(sum, func(a, b []mapset.Set[int]) bool { return len(a) < len(b) })
	return underscore.Map(sum[0],
		func(s mapset.Set[int]) MinTermRow {
			if assoc, err := underscore.Find(primes, func(tm MinTermRow) bool { return tm.Name.Equal(s) }); err == nil {
				return assoc
			}
			panic("boolean: failed Petricks method converting sum of products to min terms")
		})
}

// Generates a minimal Boolean equation equivalent to the given Boolean equation, in
// sum of product form. The major steps of the Quine-McCluskey algorithm used:
//  1. compute initial minTerms via truth table
//  2. iteratively generate set of prime implicants
//  3. determine essential prime implicants
//  4. for remaining minTerms uncovered by essential implicants, find a covering
//     implicant using Petricks method
func Minimize[T constraints.Ordered](eqn Equation[T]) Equation[T] {
	// find any rigids and flexify them so they simplify, rigidify them after minimization complete
	rigids := maps.Keys(FreeRigid(eqn))
	flex := eqn.Flexify(rigids)

	free := FreeFlex(flex)
	freeKeys := maps.Keys(free)
	slices.Sort(freeKeys)

	truth, err := truthTable(flex, freeKeys)
	if err != nil {
		panic(err)
	}

	// minTerms are elements of the truth table where the result is T.
	// It is convenient to not include the truth value element, so we remove
	// it from each row.
	minTermRows := [][]int{}
	for _, t := range truth {
		if t[len(t)-1] == MinTrue {
			minTermRows = append(minTermRows, t[:len(t)-1])
		}
	}

	// give each minTerm a unique (but meaningful) name to efficiently refer to it later
	namedMinTerms := make([]MinTermRow, len(minTermRows))
	for i, r := range minTermRows {
		namedMinTerms[i] = MinTermRow{mapset.NewSet(truthRowToInt(r)), r}
	}

	primes := primeImplicants(namedMinTerms)
	// find which implicants are essential prime implicants; these must
	// be included because they are the only implicants that cover certain minTerms
	essentials, _, remaining, uncovered := essentialImplicants(primes, namedMinTerms)

	var finalImplicants []MinTermRow
	if len(uncovered) != 0 {
		// for the remaining uncovered minTerms, there are ambiguities in which should be chosen.
		// Petrick's method is a way to systematically compute the result
		covering := petricks(remaining, uncovered)
		finalImplicants = append(essentials, covering...)
	} else {
		finalImplicants = essentials
	}

	// convert the final implicants back into equation form
	sumImplicants := underscore.Map(finalImplicants,
		func(m MinTermRow) Equation[T] { return termToSum(m, freeKeys, free) })
	sumImplicants = underscore.Unique(sumImplicants)
	minified := underscore.Reduce(
		sumImplicants,
		func(l Equation[T], r Equation[T]) Equation[T] {
			return NewOr(r, l)
		},
		Equation[T](BFalse[T]{}))

	return minified.Rigidify(rigids)
}
