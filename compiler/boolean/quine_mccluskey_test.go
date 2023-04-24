package boolean

import (
	"testing"

	"github.com/google/go-cmp/cmp"
)

func TestBooleanMinimization(t *testing.T) {
	data := []Equation[string]{
		NewFlex("a", false),
		NewAnd(NewFlex("a", false), NewFlex("a", false)),
		NewOr(NewFlex("b", false), NewFlex("b", false)),
		NewOr(NewOr(NewOr(NewOr(NewFlex("a", false), NewFlex("b", false)), NewFlex("c", false)), NewFlex("d", false)), NewFlex("e", false)),
		NewOr(NewOr(NewOr(NewOr(NewOr(NewOr(NewOr(NewFlex("a", false), NewFlex("b", false)), NewFlex("c", false)), NewFlex("d", false)), NewFlex("e", false)), NewFlex("f", false)), NewFlex("g", false)), NewFlex("h", false)),
		NewOr(NewFlex("a", false), NewAnd(NewFlex("b", false), NewFlex("c", false))),
		NewOr(NewFlex("a", true), NewFlex("b", false)),
	}

	testCases := []struct {
		name string
		exp  Equation[string]
	}{
		{
			"a --> a",
			NewFlex("a", false),
		},
		{
			"a & a --> a",
			NewFlex("a", false),
		},
		{
			"b | b --> b",
			NewFlex("b", false),
		},
		{
			"a | b | c | d | e --> a | b | c | d | e",
			NewOr(NewOr(NewOr(NewOr(NewFlex("a", false), NewFlex("b", false)), NewFlex("c", false)), NewFlex("d", false)), NewFlex("e", false)),
		},
		{
			"a | b | c | d | e | f | g | h --> a | b | c | d | e | f | g | h",
			NewOr(NewOr(NewOr(NewOr(NewOr(NewOr(NewOr(NewFlex("a", false), NewFlex("b", false)), NewFlex("c", false)), NewFlex("d", false)), NewFlex("e", false)), NewFlex("f", false)), NewFlex("g", false)), NewFlex("h", false)),
		},
		{
			"a | (b & c) --> a | (b & c)",
			NewOr(NewFlex("a", false), NewAnd(NewFlex("b", false), NewFlex("c", false))),
		},
		{
			"a... | b --> a... | b",
			NewOr(NewFlex("a", true), NewFlex("b", false)),
		},
	}

	for ind, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			res := Minimize(data[ind])
			if !cmp.Equal(res, tc.exp) {
				t.Errorf("Boolean minimization expected to make %v, got %v instead", tc.exp, res)
			}
		})
	}
}
