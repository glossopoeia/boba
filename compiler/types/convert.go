package types

import (
	"fmt"

	"github.com/glossopoeia/boba/compiler/abelian"
	"github.com/glossopoeia/boba/compiler/boolean"
	"github.com/glossopoeia/boba/compiler/kind"
)

// Convert a type into a Boolean equation. Must be only composed of Boolean
// kinded constructors or will panic.
func TypeToBooleanEquation[T int | string](ty Type[T]) boolean.Equation[T] {
	switch ct := ty.(type) {
	case TVar[T]:
		return boolean.NewFlex(ct.Name, ct.Dotted)
	case TCon[T]:
		switch ct.Name {
		case TrueName:
			return boolean.BTrue[T]{}
		case FalseName:
			return boolean.BFalse[T]{}
		}
	case TApp[T]:
		switch bt := ct.Left.(type) {
		case TCon[T]:
			switch bt.Name {
			case AndName:
				switch rt := ct.Right.(type) {
				case TApp[T]:
					return boolean.NewAnd(TypeToBooleanEquation(rt.Left), TypeToBooleanEquation(rt.Right))
				}
			case OrName:
				switch rt := ct.Right.(type) {
				case TApp[T]:
					return boolean.NewOr(TypeToBooleanEquation(rt.Left), TypeToBooleanEquation(rt.Right))
				}
			case NotName:
				return boolean.NewNot(TypeToBooleanEquation(ct.Right))
			}
		}
	}
	panic(fmt.Sprintf("types: could not convert %v to Boolean equation", ty))
}

// Convert a Boolean equation into a type made of Boolean type constructors.
func BooleanEquationToType[T int | string](eqn boolean.Equation[T], k kind.Kind[T]) Type[T] {
	switch t := eqn.(type) {
	case boolean.BTrue[T]:
		return NewTrueCtor(k)
	case boolean.BFalse[T]:
		return NewFalseCtor(k)
	case boolean.BVar[T]:
		return TVar[T]{t.Name, k, t.Dotted}
	case boolean.BNot[T]:
		return BuildNot(BooleanEquationToType(t.Elem, k))
	case boolean.BAnd[T]:
		return BuildAnd(BooleanEquationToType(t.Left, k), BooleanEquationToType(t.Right, k))
	case boolean.BOr[T]:
		return BuildOr(BooleanEquationToType(t.Left, k), BooleanEquationToType(t.Right, k))
	default:
		panic(fmt.Sprintf("types: could not convert Boolean equation %s to type", eqn.String()))
	}
}

func TypeToUnitEquation[T int | string](ty Type[T]) abelian.Equation[T, string] {
	switch ct := ty.(type) {
	case TVar[T]:
		return abelian.AbelianVariable[T, string](ct.Name)
	case TCon[T]:
		if ct.Name == AbelianOneName {
			return abelian.AbelianIdentity[T, string]()
		}
		return abelian.Equation[T, string]{Variables: map[T]int{}, Constants: map[string]int{ct.Name: 1}}
	case TApp[T]:
		switch ut := ct.Left.(type) {
		case TCon[T]:
			switch ut.Name {
			case ExponentName:
				switch at := ct.Right.(type) {
				case TApp[T]:
					scalar := at.Right.(TInt[T]).Value
					return TypeToUnitEquation(at.Left).Scale(scalar)
				}
			case MultiplyName:
				switch at := ct.Right.(type) {
				case TApp[T]:
					return TypeToUnitEquation(at.Left).Add(TypeToUnitEquation(at.Right))
				}
			}
		}
	}
	panic(fmt.Sprintf("types: could not convert type %v to Abelian equation", ty))
}

func UnitEquationToType[T int | string](eqn abelian.Equation[T, string], k kind.Kind[T]) Type[T] {
	ty := NewAbelianOneCtor(k)
	for name, exp := range eqn.Variables {
		ty = BuildMultiply(ty, BuildExponent(NewIndVar(name, k), exp))
	}
	for name, exp := range eqn.Constants {
		ty = BuildMultiply(ty, BuildExponent(Type[T](TCon[T]{name, k}), exp))
	}
	return ty
}

func TypeToFixedEquation[T int | string](ty Type[T]) abelian.Equation[T, int] {
	switch ct := ty.(type) {
	case TVar[T]:
		return abelian.AbelianVariable[T, int](ct.Name)
	case TCon[T]:
		if ct.Name == AbelianOneName {
			return abelian.AbelianIdentity[T, int]()
		}
	case TApp[T]:
		switch ut := ct.Left.(type) {
		case TCon[T]:
			switch ut.Name {
			case FixedName:
				constant := ct.Right.(TInt[T]).Value
				return abelian.Equation[T, int]{Variables: map[T]int{}, Constants: map[int]int{constant: 1}}
			case ExponentName:
				switch at := ct.Right.(type) {
				case TApp[T]:
					scalar := at.Right.(TInt[T]).Value
					return TypeToFixedEquation(at.Left).Scale(scalar)
				}
			case MultiplyName:
				switch at := ct.Right.(type) {
				case TApp[T]:
					return TypeToFixedEquation(at.Left).Add(TypeToFixedEquation(at.Right))
				}
			}
		}
	}
	panic(fmt.Sprintf("types: could not convert type %v to Abelian equation", ty))
}

func FixedEquationToType[T int | string](eqn abelian.Equation[T, int], k kind.Kind[T]) Type[T] {
	ty := NewAbelianOneCtor(k)
	for name, exp := range eqn.Variables {
		ty = BuildMultiply(ty, BuildExponent(NewIndVar(name, k), exp))
	}
	sum := 0
	for val, exp := range eqn.Constants {
		sum += val * exp
	}
	return BuildMultiply(ty, BuildFixed(sum, k))
}
