package boolean

import (
	"testing"

	"github.com/google/go-cmp/cmp"
)

func TestBooleanUnification(t *testing.T) {
	data := []struct {
		left  Equation[string]
		right Equation[string]
	}{
		{BTrue[string]{}, BTrue[string]{}},
		{BFalse[string]{}, BFalse[string]{}},
		{BTrue[string]{}, BFalse[string]{}},
		{NewFlex("a", false), NewNot(NewFlex("a", false))},
		{
			NewAnd(NewFlex("a", false), NewFlex("b", false)),
			BTrue[string]{},
		},
		{
			NewAnd(NewFlex("a", false), NewFlex("b", false)),
			BFalse[string]{},
		},
		{
			NewOr(NewFlex("a", false), NewFlex("b", false)),
			BTrue[string]{},
		},
		{
			NewOr(NewFlex("a", false), NewFlex("b", false)),
			BFalse[string]{},
		},
		{
			NewFlex("a", false),
			NewOr(NewFlex("b", false), NewFlex("c", false)),
		},
		{
			NewFlex("c", false),
			NewOr(NewFlex("a", false), NewFlex("b", false)),
		},
		{
			NewFlex("b", false),
			NewOr(NewFlex("a", false), NewFlex("c", false)),
		},
		{
			NewOr(NewFlex("a", false), NewFlex("b", false)),
			NewAnd(NewFlex("a", false), NewFlex("b", false)),
		},
	}

	testCases := []struct {
		name string
		exp  Substitution[string]
	}{
		{
			"True ~ True",
			Substitution[string]{},
		},
		{
			"False ~ False",
			Substitution[string]{},
		},
		{
			"True ~ False",
			nil,
		},
		{
			"a ~ !a",
			nil,
		},
		{
			"a & b ~ True",
			Substitution[string]{"a": BTrue[string]{}, "b": BTrue[string]{}},
		},
		{
			"a & b ~ False",
			Substitution[string]{"a": NewAnd(NewFlex("a", false), NewNot(NewFlex("b", false))), "b": NewFlex("b", false)},
		},
		{
			"a | b ~ True",
			Substitution[string]{"a": NewOr(NewFlex("a", false), NewNot(NewFlex("b", false))), "b": NewFlex("b", false)},
		},
		{
			"a | b ~ False",
			Substitution[string]{"a": BFalse[string]{}, "b": BFalse[string]{}},
		},
		{
			"a ~ b | c",
			Substitution[string]{"a": NewOr(NewFlex("b", false), NewFlex("c", false)), "b": NewFlex("b", false), "c": NewFlex("c", false)},
		},
		{
			"c ~ a | b",
			Substitution[string]{"c": NewOr(NewFlex("a", false), NewFlex("b", false)), "b": NewFlex("b", false), "a": NewFlex("a", false)},
		},
		{
			"b ~ a | c",
			Substitution[string]{"b": NewOr(NewFlex("a", false), NewFlex("c", false)), "a": NewFlex("a", false), "c": NewFlex("c", false)},
		},
		{
			"a | b ~ a & b",
			Substitution[string]{"a": NewFlex("b", false), "b": NewFlex("b", false)},
		},
	}

	for ind, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			res := Unify(data[ind].left, data[ind].right)
			if !cmp.Equal(res, tc.exp) {
				t.Errorf("Boolean minimization expected to make %v, got %v instead", tc.exp, res)
			}
		})
	}
}
