package util

import (
	"github.com/rjNemo/underscore"
	"golang.org/x/exp/maps"
)

// Optimized and does not have problems with integer overflow.
func AbsInt(n int) int {
	y := n >> 63
	return (n ^ y) - y
}

func DivFloor(n int, m int) int {
	q := n / m
	r := n % m
	if (r > 0 && m < 0) || (r < 0 && m > 0) {
		return q - 1
	}
	return q
}

func Modulo(n int, m int) int {
	r := n % m
	if (r > 0 && m < 0) || (r < 0 && m > 0) {
		return r + m
	}
	return r
}

func MapFilterValue[T comparable, V any](m map[T]V, filter func(v V) bool) map[T]V {
	res := make(map[T]V)
	for k, v := range m {
		if filter(v) {
			res[k] = v
		}
	}
	return res
}

func MergeMaps[T comparable, V any](m1 map[T]V, m2 map[T]V, combine func(v1 V, v2 V) V) map[T]V {
	res := maps.Clone(m1)
	for k, v := range m2 {
		if existing, ok := res[k]; ok {
			res[k] = combine(existing, v)
		} else {
			res[k] = v
		}
	}
	return res
}

func UniqueBy[T any, V comparable](ls []T, selector func(v T) V) []T {
	res := []T{}
	seen := []V{}
	for _, e := range ls {
		s := selector(e)
		if !underscore.Contains(seen, s) {
			seen = append(seen, s)
			res = append(res, e)
		}
	}
	return res
}

func UniqueCmp[T any](ls []T, cmp func(l T, r T) bool) []T {
	res := []T{}
	for _, e := range ls {
		equalE := func(r T) bool { return cmp(e, r) }
		_, err := underscore.Find(res, equalE)
		if err != nil {
			res = append(res, e)
		}
	}
	return res
}
