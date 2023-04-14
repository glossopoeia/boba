package compiler

import "golang.org/x/exp/maps"

// Optimized and does not have problems with integer overflow.
func absInt(n int) int {
	y := n >> 63
	return (n ^ y) - y
}

func divFloor(n int, m int) int {
	q := n / m
	r := n % m
	if (r > 0 && m < 0) || (r < 0 && m > 0) {
		return q - 1
	}
	return q
}

func modulo(n int, m int) int {
	r := n % m
	if (r > 0 && m < 0) || (r < 0 && m > 0) {
		return r + m
	}
	return r
}

func mapFilterValue[T comparable, V any](m map[T]V, filter func(v V) bool) map[T]V {
	res := make(map[T]V)
	for k, v := range m {
		if filter(v) {
			res[k] = v
		}
	}
	return res
}

func mergeMaps[T comparable, V any](m1 map[T]V, m2 map[T]V, combine func(v1 V, v2 V) V) map[T]V {
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
