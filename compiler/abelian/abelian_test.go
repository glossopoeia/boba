package abelian

import (
	"testing"

	"github.com/glossopoeia/boba/compiler/util"
	"github.com/google/go-cmp/cmp"
)

func TestAbelianMatching(t *testing.T) {
	data := []struct {
		matcher Equation[string, string]
		matchee Equation[string, string]
	}{
		{AbelianIdentity[string, string](), AbelianIdentity[string, string]()},
		{AbelianVariable[string, string]("a"), AbelianVariable[string, string]("b")},
		{
			Equation[string, string]{map[string]int{}, map[string]int{"A": 2, "B": 3}},
			Equation[string, string]{map[string]int{}, map[string]int{"B": 3, "A": 2}},
		},
		{
			Equation[string, string]{map[string]int{"x": 2, "y": 1}, map[string]int{}},
			Equation[string, string]{map[string]int{"z": 3}, map[string]int{}},
		},
		{
			Equation[string, string]{map[string]int{"x": 2}, map[string]int{}},
			Equation[string, string]{map[string]int{"x": 1, "y": 1}, map[string]int{}},
		},
		{
			Equation[string, string]{map[string]int{"x": 64, "y": -41}, map[string]int{}},
			Equation[string, string]{map[string]int{"a": 1}, map[string]int{}},
		},
	}

	testCases := []struct {
		name string
		exp  Substitution[string, string]
	}{
		{"0 ~> 0", Substitution[string, string]{}},
		{"a ~> b", Substitution[string, string]{"a": AbelianVariable[string, string]("b")}},
		{"A^2 * B^3 ~> B^3 * A^2", Substitution[string, string]{}},
		{"x^2 * y^1 ~> z^3", Substitution[string, string]{
			"x": AbelianVariable[string, string]("?0"),
			"y": Equation[string, string]{map[string]int{"?0": -2, "z": 3}, map[string]int{}},
		}},
		{"x^2 ~> x * y", nil},
		{"x^64 * y^-41 ~> a^1", Substitution[string, string]{
			"x": Equation[string, string]{map[string]int{"a": -16, "?6": -41}, map[string]int{}},
			"y": Equation[string, string]{map[string]int{"a": -25, "?6": -64}, map[string]int{}},
		}},
	}

	for ind, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			fresh := util.NewNameFresh()
			res := data[ind].matcher.Match(&fresh, data[ind].matchee)
			if !cmp.Equal(res, tc.exp) {
				t.Errorf("Abelian matching expected %v, got %v instead", tc.exp, res)
			}
		})
	}
}

func TestAbelianUnification(t *testing.T) {
	data := []struct {
		matcher Equation[string, string]
		matchee Equation[string, string]
	}{
		{AbelianVariable[string, string]("a"), AbelianVariable[string, string]("b")},
		{
			Equation[string, string]{map[string]int{}, map[string]int{"A": 2, "B": 3}},
			Equation[string, string]{map[string]int{}, map[string]int{"B": 3, "A": 2}},
		},
		{
			Equation[string, string]{map[string]int{"x": 2, "y": 1}, map[string]int{}},
			Equation[string, string]{map[string]int{"z": 3}, map[string]int{}},
		},
	}

	testCases := []struct {
		name string
		exp  Substitution[string, string]
	}{
		{"a ~> b", Substitution[string, string]{
			"a": AbelianVariable[string, string]("?1"),
			"b": AbelianVariable[string, string]("?1"),
		}},
		{"A^2 * B^3 ~> B^3 * A^2", Substitution[string, string]{}},
		{"x^2 * y^1 ~> z^3", Substitution[string, string]{
			"x": AbelianVariable[string, string]("?0"),
			"y": Equation[string, string]{map[string]int{"?0": -2, "?2": 3}, map[string]int{}},
			"z": AbelianVariable[string, string]("?2"),
		}},
	}

	for ind, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			fresh := util.NewNameFresh()
			res := data[ind].matcher.Unify(&fresh, data[ind].matchee)
			if !cmp.Equal(res, tc.exp) {
				t.Errorf("Abelian unification expected %v, got %v instead", tc.exp, res)
			}
		})
	}
}
