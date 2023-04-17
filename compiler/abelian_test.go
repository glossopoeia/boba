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
	}

	testCases := []struct {
		name string
		exp  AbelianSubstitution[string, string]
	}{
		{"0 ~> 0", AbelianSubstitution[string, string]{}},
		{"a ~> b", AbelianSubstitution[string, string]{"a": AbelianVariable[string, string]("b")}},
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
