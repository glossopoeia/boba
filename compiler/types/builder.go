package types

import "github.com/glossopoeia/boba/compiler/kind"

func BuildNot[T int | string](ty Type[T]) Type[T] {
	return TApp[T]{NewNotCtor(ty.Kind()), ty}
}

func BuildAnd[T int | string](l Type[T], r Type[T]) Type[T] {
	return TApp[T]{NewAndCtor(l.Kind()), TApp[T]{l, r}}
}

func BuildOr[T int | string](l Type[T], r Type[T]) Type[T] {
	return TApp[T]{NewOrCtor(l.Kind()), TApp[T]{l, r}}
}

func BuildExponent[T int | string](l Type[T], r Type[T]) Type[T] {
	return TApp[T]{NewExponentCtor(l.Kind()), TApp[T]{l, r}}
}

func BuildMultiply[T int | string](l Type[T], r Type[T]) Type[T] {
	return TApp[T]{NewMultiplyCtor(l.Kind()), TApp[T]{l, r}}
}

func BuildFixed[T int | string](val int, k kind.Kind[T]) Type[T] {
	return TApp[T]{NewFixedCtor(k), TInt[T]{val}}
}
