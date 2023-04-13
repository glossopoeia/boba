package compiler

import (
	"reflect"
	"testing"
)

func TestFreeString(t *testing.T) {
	data := []Kind[string]{
		SynKVar("a"),
		KBase("A", SortAbelian),
		KArrow(KBase("a", SortSyntactic), SynKVar("a")),
		KRow(BoolKVar("b")),
		KArrow(KSeq(SynKVar("a")), SynKVar("a")),
		KArrow(SynKVar("a"), KArrow(SynKVar("b"), SynKVar("a"))),
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
		SynKVar(1),
		KBase(1, SortAbelian),
		KArrow(KBase(1, SortSyntactic), SynKVar(1)),
		KRow(BoolKVar(2)),
		KArrow(KSeq(SynKVar(1)), SynKVar(1)),
		KArrow(SynKVar(1), KArrow(SynKVar(2), SynKVar(1))),
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
		{SynKVar("a"), SynKVar("b")},
		{KArrow(SynKVar("a"), SynKVar("b")), SynKVar("c")},
		{KArrow(BoolKVar("b"), SynKVar("c")), BoolKVar("b")},
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
			res := CanApplyKind(data[ind].arr, data[ind].arg)
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
		{SynKVar("a"), SynKVar("b")},
		{KArrow(SynKVar("a"), SynKVar("b")), SynKVar("c")},
		{KArrow(BoolKVar("b"), SynKVar("c")), BoolKVar("b")},
	}

	testCases := []struct {
		name   string
		expRes Kind[string]
		expErr error
	}{
		{"CantApplyNonArrow", nil, KindApplyError[string]{SynKVar("a"), SynKVar("b")}},
		{"InputNotEqualArg", nil, KindApplyError[string]{KArrow(SynKVar("a"), SynKVar("b")), SynKVar("c")}},
		{"ApplyEqual", SynKVar("c"), nil},
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
