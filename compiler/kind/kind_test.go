package kind

import (
	"reflect"
	"testing"

	"github.com/glossopoeia/boba/compiler/sort"
)

func TestFreeString(t *testing.T) {
	data := []Kind[string]{
		SynVar("a"),
		NewBase[string]("A", sort.Abelian),
		NewArrow(NewBase[string]("a", sort.Syntactic), SynVar("a")),
		NewRow(BoolVar("b")),
		NewArrow(NewSeq(SynVar("a")), SynVar("a")),
		NewArrow(SynVar("a"), NewArrow(SynVar("b"), SynVar("a"))),
	}

	testCases := []struct {
		name string
		exp  map[string]int
	}{
		{"OneVar", map[string]int{"a": 1}},
		{"NoVar", map[string]int{}},
		{"DistBase", map[string]int{"a": 1}},
		{"SubKind", map[string]int{"b": 1}},
		{"TwoOcc", map[string]int{"a": 2}},
		{"TwoVar", map[string]int{"a": 2, "b": 1}},
	}

	for ind, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			res := KindFree(data[ind])
			if !reflect.DeepEqual(res, tc.exp) {
				t.Errorf("Expected %v, got %v instead", tc.exp, res)
			}
		})
	}
}

func TestFreeInt(t *testing.T) {
	data := []Kind[int]{
		SynVar(1),
		NewBase[int]("A", sort.Abelian),
		NewArrow(NewBase[int]("A", sort.Syntactic), SynVar(1)),
		NewRow(BoolVar(2)),
		NewArrow(NewSeq(SynVar(1)), SynVar(1)),
		NewArrow(SynVar(1), NewArrow(SynVar(2), SynVar(1))),
	}

	testCases := []struct {
		name string
		exp  map[int]int
	}{
		{"OneVar", map[int]int{1: 1}},
		{"NoVar", map[int]int{}},
		{"DistBase", map[int]int{1: 1}},
		{"SubKind", map[int]int{2: 1}},
		{"TwoOcc", map[int]int{1: 2}},
		{"TwoVar", map[int]int{1: 2, 2: 1}},
	}

	for ind, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			res := KindFree(data[ind])
			if !reflect.DeepEqual(res, tc.exp) {
				t.Errorf("Expected %v, got %v instead", tc.exp, res)
			}
		})
	}
}

func TestCanApplyKind(t *testing.T) {
	data := []struct {
		arr Kind[string]
		arg Kind[string]
	}{
		{SynVar("a"), SynVar("b")},
		{NewArrow(SynVar("a"), SynVar("b")), SynVar("c")},
		{NewArrow(BoolVar("b"), SynVar("c")), BoolVar("b")},
	}

	testCases := []struct {
		name string
		exp  bool
	}{
		{"CantApplyNonArrow", false},
		{"InputNotEqualArg", false},
		{"ApplyEqual", true},
	}

	for ind, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			res := CanApply(data[ind].arr, data[ind].arg)
			if res != tc.exp {
				t.Errorf("Expected %v, got %v instead", tc.exp, res)
			}
		})
	}
}

func TestApplyKind(t *testing.T) {
	data := []struct {
		arr Kind[string]
		arg Kind[string]
	}{
		{SynVar("a"), SynVar("b")},
		{NewArrow(SynVar("a"), SynVar("b")), SynVar("c")},
		{NewArrow(BoolVar("b"), SynVar("c")), BoolVar("b")},
	}

	testCases := []struct {
		name   string
		expRes Kind[string]
		expErr error
	}{
		{"CantApplyNonArrow", nil, KindApplyError[string]{SynVar("a"), SynVar("b")}},
		{"InputNotEqualArg", nil, KindApplyError[string]{NewArrow(SynVar("a"), SynVar("b")), SynVar("c")}},
		{"ApplyEqual", SynVar("c"), nil},
	}

	for ind, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			res, err := ApplyKind(data[ind].arr, data[ind].arg)
			if res != tc.expRes {
				t.Errorf("Expected result %v, got %v instead", tc.expRes, res)
			}
			if err != tc.expErr {
				t.Errorf("Expected error %v, got %v instead", tc.expErr, err)
			}
		})
	}
}
