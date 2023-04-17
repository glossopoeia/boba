package compiler

import (
	"testing"

	"github.com/google/go-cmp/cmp"
)

func TestAbelianMatching(t *testing.T) {
	data := []struct {
		matcher AbelianEquation[string, string]
		matchee AbelianEquation[string, string]
	}{
		{AbelianIdentity[string, string](), AbelianIdentity[string, string]()},
		{AbelianVariable[string, string]("a"), AbelianVariable[string, string]("b")},
		{
			AbelianEquation[string, string]{map[string]int{}, map[string]int{"A": 2, "B": 3}},
			AbelianEquation[string, string]{map[string]int{}, map[string]int{"B": 3, "A": 2}},
		},
		{
			AbelianEquation[string, string]{map[string]int{"x": 2, "y": 1}, map[string]int{}},
			AbelianEquation[string, string]{map[string]int{"z": 3}, map[string]int{}},
		},
		{
			AbelianEquation[string, string]{map[string]int{"x": 2}, map[string]int{}},
			AbelianEquation[string, string]{map[string]int{"x": 1, "y": 1}, map[string]int{}},
		},
		{
			AbelianEquation[string, string]{map[string]int{"x": 64, "y": -41}, map[string]int{}},
			AbelianEquation[string, string]{map[string]int{"a": 1}, map[string]int{}},
		},
	}

	testCases := []struct {
		name string
		exp  AbelianSubstitution[string, string]
	}{
		{"0 ~> 0", AbelianSubstitution[string, string]{}},
		{"a ~> b", AbelianSubstitution[string, string]{"a": AbelianVariable[string, string]("b")}},
		{"A^2 * B^3 ~> B^3 * A^2", AbelianSubstitution[string, string]{}},
		{"x^2 * y^1 ~> z^3", AbelianSubstitution[string, string]{
			"x": AbelianVariable[string, string]("?0"),
			"y": AbelianEquation[string, string]{map[string]int{"?0": -2, "z": 3}, map[string]int{}},
		}},
		{"x^2 ~> x * y", nil},
		{"x^64 * y^-41 ~> a^1", AbelianSubstitution[string, string]{
			"x": AbelianEquation[string, string]{map[string]int{"a": -16, "?6": -41}, map[string]int{}},
			"y": AbelianEquation[string, string]{map[string]int{"a": -25, "?6": -64}, map[string]int{}},
		}},
	}

	for ind, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			fresh := NewNameFresh()
			res := data[ind].matcher.Match(&fresh, data[ind].matchee)
			if !cmp.Equal(res, tc.exp) {
				t.Errorf("Abelian matching expected %v, got %v instead", tc.exp, res)
			}
		})
	}
}

func TestAbelianUnification(t *testing.T) {
	data := []struct {
		matcher AbelianEquation[string, string]
		matchee AbelianEquation[string, string]
	}{
		{AbelianVariable[string, string]("a"), AbelianVariable[string, string]("b")},
		{
			AbelianEquation[string, string]{map[string]int{}, map[string]int{"A": 2, "B": 3}},
			AbelianEquation[string, string]{map[string]int{}, map[string]int{"B": 3, "A": 2}},
		},
		{
			AbelianEquation[string, string]{map[string]int{"x": 2, "y": 1}, map[string]int{}},
			AbelianEquation[string, string]{map[string]int{"z": 3}, map[string]int{}},
		},
	}

	testCases := []struct {
		name string
		exp  AbelianSubstitution[string, string]
	}{
		{"a ~> b", AbelianSubstitution[string, string]{
			"a": AbelianVariable[string, string]("?1"),
			"b": AbelianVariable[string, string]("?1"),
		}},
		{"A^2 * B^3 ~> B^3 * A^2", AbelianSubstitution[string, string]{}},
		{"x^2 * y^1 ~> z^3", AbelianSubstitution[string, string]{
			"x": AbelianVariable[string, string]("?0"),
			"y": AbelianEquation[string, string]{map[string]int{"?0": -2, "?2": 3}, map[string]int{}},
			"z": AbelianVariable[string, string]("?2"),
		}},
	}

	for ind, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			fresh := NewNameFresh()
			res := data[ind].matcher.Unify(&fresh, data[ind].matchee)
			if !cmp.Equal(res, tc.exp) {
				t.Errorf("Abelian unification expected %v, got %v instead", tc.exp, res)
			}
		})
	}
}
