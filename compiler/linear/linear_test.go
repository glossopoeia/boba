package linear

import (
	"testing"
	"testing/quick"

	"github.com/google/go-cmp/cmp"
)

func TestLinearEquationSolution(t *testing.T) {
	data := []Equation{
		{[]int{}, []int{}},         // empty equation
		{[]int{5, 10}, []int{18}},  // 5x + 10y = 18
		{[]int{5, 3}, []int{0}},    // 5x + 3y = 0
		{[]int{64, -41}, []int{1}}, // 64x - 41y = 1
	}

	testCases := []struct {
		name string
		exp  Substitution
	}{
		{"EmptyEqn", nil},
		{"5x+10y=18", nil},
		{"5x+3y=0",
			Substitution{
				0: Equation{[]int{0, 0, 0, 3}, []int{0}},
				1: Equation{[]int{0, 0, 0, -5}, []int{0}},
			}},
		{"64x-41y=1",
			Substitution{
				0: Equation{[]int{0, 0, 0, 0, 0, 0, -41}, []int{-16}},
				1: Equation{[]int{0, 0, 0, 0, 0, 0, -64}, []int{-25}},
			}},
	}

	for ind, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			res := data[ind].Solution()
			if !cmp.Equal(res, tc.exp) {
				t.Errorf("Expected %v, got %v instead", tc.exp, res)
			}
		})
	}
}

func TestLinearSolutionProperties(t *testing.T) {

	// equations of the form Ax = 0 always have solution 0
	singleVarEqualsZeroIsZero :=
		func(coeff int) bool {
			if coeff == 0 {
				return true
			}

			eqn := Equation{[]int{coeff}, []int{0}}
			sol := Substitution{0: Equation{[]int{0}, []int{0}}}
			return cmp.Equal(eqn.Solution(), sol)
		}

	// equations of the form Ax + Ay = 0 always have solution 0, -1
	twoVarsEqualZeroSameCoeffIsSubtraction :=
		func(coeff int) bool {
			if coeff == 0 {
				return true
			}

			eqn := Equation{[]int{coeff, coeff}, []int{0}}
			sol := Substitution{0: Equation{[]int{0, -1}, []int{0}}}
			return cmp.Equal(eqn.Solution(), sol)
		}

	if err := quick.Check(singleVarEqualsZeroIsZero, nil); err != nil {
		t.Errorf("Equation of form Ax = 0 had incorrect solution with A: %v", err)
	}

	if err := quick.Check(twoVarsEqualZeroSameCoeffIsSubtraction, nil); err != nil {
		t.Errorf("Equation of form Ax + Ay = 0 had incorrect solution with A: %v", err)
	}
}
