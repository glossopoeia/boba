package util

type Dotted[T any] struct {
	Dotted bool
	Elem   T
}

type Dots[T any] []Dotted[T]
