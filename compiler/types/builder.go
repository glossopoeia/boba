package types

import (
	"github.com/glossopoeia/boba/compiler/kind"
	"github.com/glossopoeia/boba/compiler/util"
)

func BuildNot[T int | string](ty Type[T]) Type[T] {
	return TApp[T]{NewNotCtor(ty.Kind()), ty}
}

func BuildAnd[T int | string](l Type[T], r Type[T]) Type[T] {
	return TApp[T]{NewAndCtor(l.Kind()), TApp[T]{l, r}}
}

func BuildOr[T int | string](l Type[T], r Type[T]) Type[T] {
	return TApp[T]{NewOrCtor(l.Kind()), TApp[T]{l, r}}
}

func BuildExponent[T int | string](l Type[T], exp int) Type[T] {
	return TApp[T]{NewExponentCtor(l.Kind()), TApp[T]{l, TInt[T]{exp}}}
}

func BuildMultiply[T int | string](l Type[T], r Type[T]) Type[T] {
	return TApp[T]{NewMultiplyCtor(l.Kind()), TApp[T]{l, r}}
}

func BuildFixed[T int | string](val int, k kind.Kind[T]) Type[T] {
	return TApp[T]{NewFixedCtor(k), TInt[T]{val}}
}

func BuildField[T int | string](name string, ty Type[T]) Type[T] {
	return TApp[T]{NewFieldCtor[T](name), ty}
}

// Apply the given constraints to the given type, returning the result as a single combined type.
func BuildQualifiedType[T int | string](constraints []util.Dotted[Type[T]], head Type[T]) Type[T] {
	return TApp[T]{
		TApp[T]{
			NewConstrainedCtor[T](),
			TApp[T]{
				NewConstraintsCtor[T](),
				NewSeq(constraints, kind.NewConstraint[T]())}},
		head}
}
