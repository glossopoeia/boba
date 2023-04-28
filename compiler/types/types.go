package types

import (
	"github.com/glossopoeia/boba/compiler/kind"
	"github.com/glossopoeia/boba/compiler/util"
	"github.com/rjNemo/underscore"
)

const (
	FunctionName    string = "-->"
	TrackedName     string = "Tracked"
	ConstrainedName string = "Constrained"
	ConstraintsName string = "Constraints"
	ListName        string = "List"
	TupleName       string = "Tuple"
	RecordName      string = "Record"
	VariantName     string = "Variant"
	// The wildcard type in Boba is used for defining some overloaded method instance types. It never
	// appears in a concrete type, instead always being replaced by a new fresh variable when instantiated.
	WildcardName   string = "_"
	TrueName       string = "True"
	FalseName      string = "False"
	AndName        string = "&"
	OrName         string = "|"
	NotName        string = "!"
	AbelianOneName string = "."
	ExponentName   string = "^"
	MultiplyName   string = "*"
	FixedName      string = "Fixed"

	BoolName        string = "Bool"
	RuneName        string = "Rune"
	StringName      string = "String"
	RefName         string = "Ref"
	NurseryName     string = "Nursery"
	CancelTokenName string = "CancelToken"
	StateName       string = "st!"
	IterName        string = "iter!"
)

const (
	I8Name      string = "I8"
	U8Name      string = "U8"
	I16Name     string = "I16"
	U16Name     string = "U16"
	I32Name     string = "I32"
	U32Name     string = "U32"
	I64Name     string = "I64"
	U64Name     string = "U64"
	INativeName string = "INative"
	UNativeName string = "UNative"
	F32         string = "F32"
	F64         string = "F64"
)

type Type[T int | string] interface {
	Kind() kind.Kind[T]
}

type TCon[T int | string] struct {
	Name     string
	CtorKind kind.Kind[T]
}

func (t TCon[T]) Kind() kind.Kind[T] {
	return t.CtorKind
}

type TVar[T int | string] struct {
	Name    T
	VarKind kind.Kind[T]
	Dotted  bool
}

func NewIndVar[T int | string](name T, k kind.Kind[T]) Type[T] {
	return TVar[T]{name, k, false}
}

func (t TVar[T]) Kind() kind.Kind[T] {
	return t.VarKind
}

type TInt[T int | string] struct {
	Value int
}

func (t TInt[T]) Kind() kind.Kind[T] {
	return kind.NewInt[T]()
}

type TApp[T int | string] struct {
	Left  Type[T]
	Right Type[T]
}

func (t TApp[T]) Kind() kind.Kind[T] {
	applied, err := kind.ApplyKind(t.Left.Kind(), t.Right.Kind())
	if err != nil {
		panic(err)
	}
	return applied
}

type TRow[T int | string] struct {
	Row      []util.Dotted[Type[T]]
	ElemKind kind.Kind[T]
	Ordered  bool
}

func (row TRow[T]) Kind() kind.Kind[T] {
	isSeq := func(t util.Dotted[Type[T]]) bool {
		switch t.Elem.(type) {
		case TRow[T]:
			return true
		default:
			return false
		}
	}

	if underscore.Any(row.Row, isSeq) && underscore.Any(row.Row, func(t util.Dotted[Type[T]]) bool { return !isSeq(t) }) {
		panic("types: mixed data and nested rows in row type")
	}
	if underscore.Any(row.Row, func(t util.Dotted[Type[T]]) bool { return t.Elem.Kind() != row.ElemKind }) {
		panic("types: actual row element kind did not match specified kind")
	}

	if row.Ordered {
		return kind.NewSeq(row.ElemKind)
	} else {
		return kind.NewRow(row.ElemKind)
	}
}

// The function type in Boba carries a lot more information than just inputs and outputs.
// It also tells what 'effects' it performs, what 'permissions' it requires from the context
// it runs in, and whether or not the compiler believes it is 'total'. All three of these attributes
// depend on the operations used within the body of the function, and can be inferred during
// type inference.
func NewFunctionCtor[T int | string]() Type[T] {
	return TCon[T]{
		FunctionName,
		kind.NewArrow(
			kind.NewRow(kind.NewEffect[T]()),
			kind.NewArrow(
				kind.NewPermission[T](),
				kind.NewArrow(
					kind.NewTotality[T](),
					kind.NewArrow(
						kind.NewSeq(kind.NewValue[T]()),
						kind.NewArrow(
							kind.NewSeq(kind.NewValue[T]()),
							kind.NewData[T]()))))),
	}
}

// A tracked value is a data type with a sharing and validity annotation applied to it.
// Since sharing analysis is so viral, value-kinded types end up being the arguments
// required by most other types, since in Boba a data type without a sharing annotation
// cannot be inhabited by any values.
func NewTrackedCtor[T int | string]() Type[T] {
	return TCon[T]{
		TrackedName,
		kind.NewArrow(
			kind.NewData[T](),
			kind.NewArrow(
				kind.NewShare[T](),
				kind.NewValue[T]())),
	}
}

// Since Boba supports a form of variable-arity polymorphism, we also need to have tuples
// of constraints, which can be variable-arity. This allows for things like a generic
// tuple equality function supporting variable arity polymorphism.
func NewConstraintsCtor[T int | string]() Type[T] {
	return TCon[T]{
		ConstraintsName,
		kind.NewArrow(
			kind.NewSeq(kind.NewConstraint[T]()),
			kind.NewConstraint[T]()),
	}
}

// Function types in Boba can be 'qualified' by a set of constraints. These constraints help
// to drive type inference and allow a powerful form of ad-hoc polymorphism, similar to
// Haskell's typeclass constraints. This constructor allows us to represent qualified types
// as just another form of type, but it should really only occur as an outermost type
// constructor since it doesn't make a lot of sense for constraints to be nested in types.
func NewConstrainedCtor[T int | string]() Type[T] {
	return TCon[T]{
		ConstrainedName,
		kind.NewArrow(
			kind.NewConstraint[T](),
			kind.NewArrow(
				kind.NewValue[T](),
				kind.NewValue[T]())),
	}
}

func NewWildcardCtor[T int | string](k kind.Kind[T]) Type[T] {
	return TCon[T]{WildcardName, k}
}

func NewTrueCtor[T int | string](k kind.Kind[T]) Type[T] {
	return TCon[T]{TrueName, k}
}

func NewFalseCtor[T int | string](k kind.Kind[T]) Type[T] {
	return TCon[T]{FalseName, k}
}

func NewAndCtor[T int | string](k kind.Kind[T]) Type[T] {
	return TCon[T]{AndName, kind.NewArrow(k, kind.NewArrow(k, k))}
}

func NewOrCtor[T int | string](k kind.Kind[T]) Type[T] {
	return TCon[T]{OrName, kind.NewArrow(k, kind.NewArrow(k, k))}
}

func NewNotCtor[T int | string](k kind.Kind[T]) Type[T] {
	return TCon[T]{NotName, kind.NewArrow(k, k)}
}

func NewAbelianOneCtor[T int | string](k kind.Kind[T]) Type[T] {
	return TCon[T]{AbelianOneName, k}
}

func NewExponentCtor[T int | string](k kind.Kind[T]) Type[T] {
	return TCon[T]{ExponentName, kind.NewArrow(k, kind.NewArrow(kind.NewInt[T](), k))}
}

func NewMultiplyCtor[T int | string](k kind.Kind[T]) Type[T] {
	return TCon[T]{MultiplyName, kind.NewArrow(k, kind.NewArrow(k, k))}
}

func NewFixedCtor[T int | string](k kind.Kind[T]) Type[T] {
	return TCon[T]{FixedName, kind.NewArrow(kind.NewInt[T](), k)}
}

func NewBoolCtor[T int | string]() Type[T] {
	return TCon[T]{BoolName, kind.NewData[T]()}
}

func NewNumericCtor[T int | string](numName string) Type[T] {
	return TCon[T]{numName, kind.NewArrow(kind.NewMeasure[T](), kind.NewData[T]())}
}

func NewRuneCtor[T int | string]() Type[T] {
	return TCon[T]{RuneName, kind.NewArrow(kind.NewTrust[T](), kind.NewArrow(kind.NewClear[T](), kind.NewData[T]()))}
}

func NewStringCtor[T int | string]() Type[T] {
	return TCon[T]{StringName, kind.NewArrow(kind.NewTrust[T](), kind.NewArrow(kind.NewClear[T](), kind.NewData[T]()))}
}

func NewRefCtor[T int | string]() Type[T] {
	return TCon[T]{RefName, kind.NewArrow(kind.NewHeap[T](), kind.NewArrow(kind.NewValue[T](), kind.NewData[T]()))}
}

func NewNurseryCtor[T int | string]() Type[T] {
	return TCon[T]{NurseryName, kind.NewArrow(kind.NewHeap[T](), kind.NewData[T]())}
}

func NewCancelTokenCtor[T int | string]() Type[T] {
	return TCon[T]{CancelTokenName, kind.NewData[T]()}
}

func NewStateCtor[T int | string]() Type[T] {
	return TCon[T]{StateName, kind.NewArrow(kind.NewHeap[T](), kind.NewEffect[T]())}
}

func NewIterCtor[T int | string]() Type[T] {
	return TCon[T]{IterName, kind.NewArrow(kind.NewValue[T](), kind.NewEffect[T]())}
}

func NewListCtor[T int | string]() Type[T] {
	return TCon[T]{ListName, kind.NewArrow(kind.NewData[T](), kind.NewData[T]())}
}

func NewTupleCtor[T int | string]() Type[T] {
	return TCon[T]{IterName, kind.NewArrow(kind.NewSeq(kind.NewValue[T]()), kind.NewData[T]())}
}

func NewRecordCtor[T int | string]() Type[T] {
	return TCon[T]{RecordName, kind.NewArrow(kind.NewRow(kind.NewField[T]()), kind.NewData[T]())}
}

func NewVariantCtor[T int | string]() Type[T] {
	return TCon[T]{VariantName, kind.NewArrow(kind.NewRow(kind.NewField[T]()), kind.NewData[T]())}
}

// A string, rune, or byte array has a trust attribute. The value is 'trusted' for inclusion
// into database or for execution/evaluation if the attribute is True.
func NewTrustCtor[T int | string]() Type[T] {
	return NewTrueCtor(kind.NewTrust[T]())
}

// A string, rune, or byte array has a trust attribute. The value is 'distrusted' for inclusion
// into database or for execution/evaluation if the attribute is False.
func NewDistrustCtor[T int | string]() Type[T] {
	return NewFalseCtor(kind.NewTrust[T]())
}

// A string, rune, or byte array has a clearance attribute. The value is 'clear' for output
// to a user or consuming program if the attribute is True.
func NewClearCtor[T int | string]() Type[T] {
	return NewTrueCtor(kind.NewClear[T]())
}

// A string, rune, or byte array has a clearance attribute. The value is 'secret' for output
// to a user or consuming program if the attribute is False.
func NewSecretCtor[T int | string]() Type[T] {
	return NewFalseCtor(kind.NewClear[T]())
}
