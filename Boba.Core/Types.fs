namespace Boba.Core

module Types =

    open System.Diagnostics
    open Common
    open Fresh
    open Kinds

    /// Rather than duplicating a lot of different constructors throughout the pipeline, we enumerate the separate sizes of integers
    /// here for re-use. Integers are mostly treated the same other than their size.
    type IntegerSize =
        | I8 | U8
        | I16 | U16
        | I32 | U32
        | I64 | U64
        | ISize | USize

    let integerSizeFnSuffix intSize =
        match intSize with
        | I8 -> "i8"
        | U8 -> "u8"
        | I16 -> "i16"
        | U16 -> "u16"
        | I32 -> "i32"
        | U32 -> "u32"
        | I64 -> "i64"
        | U64 -> "u64"
        | ISize -> "isize"
        | USize -> "usize"

    /// Rather than duplicating a lot of different constructors throughout the pipeline, we enumerate the separate sizes of floats
    /// here for re-use. Floating-point numbers are mostly treated the same other than their size.
    [<DebuggerDisplay("{ToString()}")>]
    type FloatSize =
        | Single
        | Double

    let floatSizeFnSuffix floatSize =
        match floatSize with
        | Single -> "f32"
        | Double -> "f64"


    /// It is convenient throughout the implementation of the type system to be able to pattern match on some primitive type
    /// constructors. Using the standard type constructor, and making the primitives constants, would result in pattern matching
    /// on the string name of the primitive, which is bug prone and far less maintainable. However, we don't want to clutter the
    /// Type data structure with noisy type constants, so the primitives have been separated out here.
    [<DebuggerDisplay("{ToString()}")>]
    type PrimType =
        /// A value is a data type with a sharing and validity annotation applied to it.
        /// Since sharing analysis is so viral, value-kinded types end up being the arguments
        /// required by most other types, since in Boba a data type without a sharing annotation
        /// cannot be inhabited by any values.
        | PrValue
        /// Built-in Boolean type, with values representing true and false.
        | PrBool
        /// The various fixed-size integer types in Boba can all be parameterized by 'unit' types by default.
        | PrInteger of IntegerSize
        /// The various floating-point number types in Boba can all be parameterized by 'unit' types by default.
        | PrFloat of FloatSize
        /// The function type in Boba carries a lot more information than just inputs and outputs.
        /// It also tells what 'effects' it performs, what 'permissions' it requires from the context
        /// it runs in, and whether or not the compiler believes it is 'total'. All three of these attributes
        /// depend on the operations used within the body of the function, and can be inferred during
        /// type inference.
        | PrFunction
        | PrRef
        | PrState

        // Collection
        | PrTuple
        | PrList
        | PrVector
        | PrSlice

        // Structural
        | PrRecord
        | PrVariant
        override this.ToString () =
            match this with
            | PrValue -> "Val"
            | PrBool -> "Bool"
            | PrFunction -> "-->"
            | PrRef -> "Ref"
            | PrState -> "State"
            | PrTuple -> "Tuple"
            | PrList -> "List"
            | PrVector -> "Vector"
            | PrSlice -> "Slice"
            | PrRecord -> "Record"
            | PrVariant -> "Variant"
            | PrInteger k -> $"{k}"
            | PrFloat k -> $"{k}"

    let primKind prim =
        match prim with
        | PrValue -> karrow KData (karrow KValidity (karrow KSharing KValue))
        | PrBool -> KData
        | PrInteger _ -> karrow KUnit KData
        | PrFloat _ -> karrow KUnit KData
        | PrFunction -> karrow (KRow KEffect) (karrow (KRow KPermission) (karrow KTotality (karrow (kseq KValue) (karrow (kseq KValue) KData))))
        | PrRef -> karrow KHeap (karrow KValue KData)
        | PrState -> karrow KHeap KEffect

        | PrTuple -> karrow (kseq KValue) KData
        | PrList -> karrow KValue KData
        | PrVector -> karrow KFixed (karrow KValue KData)
        | PrSlice -> karrow KFixed (karrow KValue KData)

        | PrRecord -> karrow (KRow KField) KData
        | PrVariant -> karrow (KRow KField) KData

    /// The type system of Boba extends a basic constructor-polymorphic capable Hindley-Milner type system with several 'base types' that
    /// essentially drive different unification algorithms, as well as 'dotted sequence types' which support variable arity polymorphism.
    /// Note that the interaction between variable-arity polymorphism and the 'shared' type is not currently as nice as it could be; we
    /// would need to add 'dot-to-disjunction' functionality to boolean equations for tuples to get proper sharing polymorphism in the
    /// presence of sharing attributes.
    /// 
    /// Types are built up from the base types using either TSeq or TApp. All source-code explicit primitive types should be
    /// desugared into this form before type inference is started.
    ///
    /// Unique/shared types appear as attributes on type constructors that represent 'complete' data types (i.e. not on unapplied type
    /// constructors. Shared types unify via Boolean unification, where true represents 'Unique/Linear' and false represents 'Shared'.
    /// The intent of sharing attributes on data types is to allow a program to specify that a type should not have been/should not
    /// be duplicated, and have this assertion tracked throughout the lifetime of the data/resource.
    [<DebuggerDisplay("{ToString()}")>]
    type Type =
        /// A type variable stands in for a particular type, or a sequence of types. The indexes component allows this variable to
        /// select down n levels in a 'sequence substitution', where n is the length of the indexes list. This feature eliminates the
        /// need for generating fresh variables during substitution, which would otherwise greatly complicate sequence substitution
        /// during type inference.
        | TVar of name: string * kind: Kind
        /// A dotted type variable stands in for a sequence of types. The primary impetus for including this is in Boolean equation
        /// types that exist outside of sequences, but still reference variables that can be substituted with a sequence. Basically,
        /// a tuple type ((a^u)...)^u... has type variable u occuring inside the sequence in the tuple as a TVar, and outside the
        /// tuple (not in a sequence) as a TDotVar.
        | TDotVar of name: string * kind: Kind
        /// Represents a rigid type constructor with an explicit kind. Equality of type constructors is based on both name and kind.
        | TCon of name: string * kind: Kind
        /// Special handler for C pointer types.
        | TPtr of name: string
        | TPrim of prim: PrimType

        | TTrue of kind: Kind
        | TFalse of kind: Kind
        | TAnd of left: Type * right: Type
        | TOr of left: Type * right: Type
        | TNot of body: Type

        | TAbelianOne of kind: Kind // identity type for any kind of abelian equation
        | TExponent of body: Type * power: int
        | TMultiply of left: Type * right: Type
        | TFixedConst of num: int // for the numeric constants of fixed size types

        /// Kind argument here is not the kind of the constructor, but the kind of the elements stored in the row.
        | TRowExtend of kind: Kind
        /// Kind argument here is not the kind of the constructor, but the kind of the elements stored in the row.
        | TEmptyRow of kind: Kind

        | TSeq of seq: DotSeq.DotSeq<Type>
        | TApp of cons: Type * arg: Type
        override this.ToString () =
            match this with
            | TVar (n, k) -> $"{n}"
            | TDotVar (n, k) -> $"{n}..."
            | TCon (n, k) -> n
            | TPtr n -> $"{n}*"
            | TPrim n -> $"{n}"
            | TTrue KSharing -> "unique"
            | TFalse KSharing -> "shared"
            | TTrue KTotality -> "total"
            | TFalse KTotality -> "partial"
            | TTrue KValidity -> "validated"
            | TFalse KValidity -> "unvalidated"
            | TTrue _ -> "true?"
            | TFalse _ -> "false?"
            | TAnd (l, r) -> $"({l} ∧ {r})"
            | TOr (l, r) -> $"({l} ∨ {r})"
            | TNot b -> $"!{b}"
            | TAbelianOne k -> ""
            | TExponent (b, p) -> $"{b}^{p}"
            | TMultiply (l, r) -> $"({l}{r})"
            | TFixedConst n -> $"{n}"
            | TRowExtend k -> "rowCons"
            | TEmptyRow k -> "."
            | TSeq ts -> $"<{ts}>"
            | TApp (TApp (TApp (TPrim PrValue, (TApp _ as d)), v), s) -> $"{{({d}) {v} {s}}}"
            | TApp (TApp (TApp (TPrim PrValue, d), v), s) -> $"{{{d} {v} {s}}}"
            | TApp (l, (TApp (TApp (TApp (TPrim PrValue, _), _), _) as r)) -> $"{l} {r}"
            | TApp (l, (TApp _ as r)) -> $"{l} ({r})"
            | TApp (l, r) -> $"{l} {r}"

    /// 'Single predicates' are constraints on a type as we know them from Haskell, the 'Eq a' in the type 'Eq a => a -> a -> bool'.
    /// Boba, however, requires 'multi predicates' to be able to support typeclasses over variable arity polymorphism, for tuples and
    /// (more importantly) functions. For instances, we need to be able to support 'instance Eq a => Eq (Tuple a...)', and have the substitution
    /// of 'a' in the predicate expand into multiple predicates.
    ///
    /// Part of the trouble here is a dictionary-passing problem. From the definition of an overloaded function with a variable arity predicate,
    /// it is no longer possible to know how many dictionaries will be passed to the function based on the type signature. Indeed, the number of
    /// dictionaries to be passed now varies with the size of the tuple, or function input/output sequence, that is constrained by the predicate.
    ///
    /// One solution is to have 'predicate tuples'. This solution is nice because it's just an extension of the dictionary-passing semantics. So
    /// the 'multi predicate' is in fact a tuple of predicates, and multi predicates can be nested just as variable arity tuples can, provided all
    /// the same restrictions about nesting variable arity polymorphism apply. So now the instance type above looks like
    /// 'instance (Eq a...) => Eq (Tuple a...)', and the definition is elaborated into a function that takes a tuple of Eq dictionaries as a parameter,
    /// instead of just a single dictionary.
    ///
    /// The other way to implement this is to just do monomorphization, which eliminates all variable arity definitions so that there's nothing to
    /// worry about. The reason to prefer multi predicates here, is so that we better support separate compilation for alternative implementations
    /// of Boba.
    type Predicate = { Name: string; Argument: Type }

    type QualifiedType =
        { Context: List<Predicate>; Head: Type }
        override this.ToString() = if this.Context.IsEmpty then $"{this.Head}" else $"{this.Context} => {this.Head}"

    type TypeScheme =
        { Quantified: List<(string * Kind)>; Body: QualifiedType }
        override this.ToString() = $"{this.Body}"

    type RowType = { Elements: List<Type>; RowEnd: Option<string>; ElementKind: Kind }


    // Type sequence utilities
    let isSeq t =
        match t with
        | TSeq _ -> true
        | _ -> false

    let isInd t =
        match t with
        | TSeq _ -> false
        | _ -> true

    let getSeq t =
        match t with
        | TSeq ts -> ts
        | _ -> failwith "Called getSeq on non-TSeq"

    let emptySeqOrInd (t : Type) =
        match t with
        | TSeq (DotSeq.SEnd) -> true
        | TSeq (_) -> false
        | _ -> true


    // Functional constructors
    let validAttr = TTrue KValidity
    let invalidAttr = TFalse KValidity
    let totalAttr = TTrue KTotality
    let partialAttr = TFalse KTotality
    let uniqueAttr = TTrue KSharing
    let sharedAttr = TFalse KSharing

    let typeVar name kind = TVar (name, kind)
    let typeDotVar name kind = TDotVar (name, kind)
    let typeCon name kind = TCon (name, kind)
    let typeApp cons arg = TApp (cons, arg)

    let typeNot n = TNot n
    let typeOr l r = TOr (l, r)
    let typeAnd l r = TAnd (l, r)

    let typeExp b n = TExponent (b, n)
    let typeMul l r = TMultiply (l, r)

    let typeField name ty = typeApp (typeCon name (karrow KValue KField)) ty
 
    let qualType context head = { Context = context; Head = head }

    let schemeType quantified body = { Quantified = quantified; Body = body }

    let rec typeToBooleanEqn ty =
        match ty with
        | TTrue _ -> Boolean.BTrue
        | TFalse _ -> Boolean.BFalse
        | TVar (n, k) when isKindBoolean k -> Boolean.BVar n
        | TDotVar (n, k) when isKindBoolean k -> Boolean.BDotVar n
        | TAnd (l, r) -> Boolean.BAnd (typeToBooleanEqn l, typeToBooleanEqn r)
        | TOr (l, r) -> Boolean.BOr (typeToBooleanEqn l, typeToBooleanEqn r)
        | TNot n -> Boolean.BNot (typeToBooleanEqn n)
        | _ -> failwith "Tried to convert a non-Boolean type to a Boolean equation"

    let rec booleanEqnToType kind eqn =
        match eqn with
        | Boolean.BTrue -> TTrue kind
        | Boolean.BFalse -> TFalse kind
        | Boolean.BVar n -> TVar (n, kind)
        | Boolean.BDotVar n -> TDotVar (n, kind)
        | Boolean.BRigid n -> TVar (n, kind)
        | Boolean.BDotRigid n -> TDotVar (n, kind)
        | Boolean.BAnd (l, r) -> TAnd (booleanEqnToType kind l, booleanEqnToType kind r)
        | Boolean.BOr (l, r) -> TOr (booleanEqnToType kind l, booleanEqnToType kind r)
        | Boolean.BNot n -> TNot (booleanEqnToType kind n)
    
    let attrsToDisjunction kind attrs =
        List.map typeToBooleanEqn attrs
        |> List.fold (fun eqn tm -> Boolean.BOr (eqn, tm)) Boolean.BFalse
        |> Boolean.minimize
        |> booleanEqnToType kind

    let attrsToConjunction kind attrs =
        List.map typeToBooleanEqn attrs
        |> List.fold (fun eqn tm -> Boolean.BAnd (eqn, tm)) Boolean.BTrue
        |> Boolean.minimize
        |> booleanEqnToType kind

    let rec unitEqnToType (eqn : Abelian.Equation<string, string>) =
        typeMul
            (Map.fold (fun ty var exp -> typeMul ty (typeExp (typeVar var KUnit) exp)) (TAbelianOne KUnit) eqn.Variables)
            (Map.fold (fun ty unit exp -> typeMul ty (typeExp (typeCon unit KUnit) exp)) (TAbelianOne KUnit) eqn.Constants)

    let rec typeToUnitEqn ty =
        match ty with
        | TAbelianOne _ -> new Abelian.Equation<string, string>()
        | TVar (n, KUnit) -> new Abelian.Equation<string, string>(n)
        | TCon (n, KUnit) -> new Abelian.Equation<string, string>(Map.empty, Map.add n 1 Map.empty)
        | TMultiply (l, r) -> (typeToUnitEqn l).Add(typeToUnitEqn r)
        | TExponent (b, n) -> (typeToUnitEqn b).Scale(n)
        | _ -> failwith "Tried to convert a non-Abelian type to a unit equation"

    let rec fixedEqnToType (eqn: Abelian.Equation<string, int>) =
        typeMul
            (Map.fold (fun ty var exp -> typeMul ty (typeExp (typeVar var KUnit) exp)) (TAbelianOne KFixed) eqn.Variables)
            (Map.fold (fun ty fix exp -> typeMul ty (typeExp (TFixedConst fix) exp)) (TAbelianOne KFixed) eqn.Constants)

    let rec typeToFixedEqn ty =
        match ty with
        | TAbelianOne _ -> new Abelian.Equation<string, int>()
        | TVar (n, KUnit) -> new Abelian.Equation<string, int>(n)
        | TFixedConst n -> new Abelian.Equation<string, int>(Map.empty, Map.add n 1 Map.empty)
        | TMultiply (l, r) -> (typeToFixedEqn l).Add(typeToFixedEqn r)
        | TExponent (b, n) -> (typeToFixedEqn b).Scale(n)
        | _ -> failwith "Tried to convert a non-Abelian type to a unit equation"

    let rec typeToRow ty =
        match ty with
        | TApp (TApp (TRowExtend k, elem), row) ->
            let { Elements = elems; RowEnd = rowEnd; ElementKind = elemKind } = typeToRow row
            if elemKind = k
            then { Elements = elem :: elems; RowEnd = rowEnd; ElementKind = elemKind }
            else failwith "Mismatch in row kinds"
        | TVar (row, KRow k) -> { Elements = []; RowEnd = Some row; ElementKind = k }
        | TEmptyRow k -> { Elements = []; RowEnd = None; ElementKind = k }
        | _ -> failwith "Tried to convert a non-row type to a field row."

    let rec rowToType row =
        match row.Elements with
        | e :: es -> typeApp (typeApp (TRowExtend row.ElementKind) e) (rowToType { row with Elements = es })
        | [] ->
            match row.RowEnd with
            | Some r -> typeVar r (KRow row.ElementKind)
            | None -> TEmptyRow row.ElementKind

    let rec rowElementHead rowElem =
        match rowElem with
        | TApp (spine, _) -> rowElementHead spine
        | TCon _ -> rowElem
        | TPrim _ -> rowElem
        | _ -> failwith "Improperly structured row element head"



    // Free variable computations
    let rec typeFreeWithKinds t =
        match t with
        | TVar (n, k) -> Set.singleton (n, k)
        | TDotVar (n, k) -> Set.singleton (n, k)
        | TSeq ts -> DotSeq.toList ts |> List.map typeFreeWithKinds |> Set.unionMany
        | TApp (l, r) -> Set.union (typeFreeWithKinds l) (typeFreeWithKinds r)

        | TAnd (l, r) -> Set.union (typeFreeWithKinds l) (typeFreeWithKinds r)
        | TOr (l, r) -> Set.union (typeFreeWithKinds l) (typeFreeWithKinds r)
        | TNot n -> typeFreeWithKinds n

        | TExponent (b, _) -> typeFreeWithKinds b
        | TMultiply (l, r) -> Set.union (typeFreeWithKinds l) (typeFreeWithKinds r)

        | _ -> Set.empty

    let predFreeWithKinds p = typeFreeWithKinds p.Argument

    let contextFreeWithKinds c = List.map predFreeWithKinds c |> Set.unionMany

    let qualFreeWithKinds q = contextFreeWithKinds q.Context |> Set.union (typeFreeWithKinds q.Head)

    let typeFree = typeFreeWithKinds >> Set.map fst

    let predFree p = typeFree p.Argument

    let contextFree c = List.map predFree c |> Set.unionMany

    let qualFree q = contextFree q.Context |> Set.union (typeFree q.Head)

    let schemeFree s = Set.difference (qualFree s.Body) (Set.ofList (List.map fst s.Quantified))


    // Kind computations
    exception MixedDataAndNestedSequences of DotSeq.DotSeq<Type>
    exception KindNotExpected of Kind * List<Kind>
    exception KindInvalidInContext of Kind

    let expectKindsExn pred expected test =
        if pred expected
        then 
            if List.forall (fun t -> t = expected && pred t) test
            then expected
            else raise (KindNotExpected (expected, test))
        else raise (KindInvalidInContext expected)

    let expectKindPredExn pred test =
        if pred test
        then test
        else raise (KindInvalidInContext test)

    let rec typeKindExn t =
        match t with
        | TVar (_, k) -> k
        | TDotVar (_, k) -> k
        | TCon (_, k) -> k
        | TPtr _ -> KData
        | TPrim p -> primKind p

        | TTrue k -> expectKindPredExn isKindBoolean k
        | TFalse k -> expectKindPredExn isKindBoolean k
        | TAnd (l, r) -> expectKindsExn isKindBoolean (typeKindExn l) [(typeKindExn r)]
        | TOr (l, r) -> expectKindsExn isKindBoolean (typeKindExn l) [(typeKindExn r)]
        | TNot n -> expectKindPredExn isKindBoolean (typeKindExn n)

        | TAbelianOne k -> expectKindPredExn isKindAbelian k
        | TExponent (b, _) -> expectKindPredExn isKindAbelian (typeKindExn b)
        | TMultiply (l, r) -> expectKindsExn isKindAbelian (typeKindExn l) [(typeKindExn r)]
        | TFixedConst _ -> KFixed

        | TRowExtend k -> karrow k (karrow (KRow k) (KRow k))
        | TEmptyRow k -> KRow k

        | TSeq ts ->
            match ts with
            | ts when DotSeq.all isInd ts -> KSeq KValue
            | ts when DotSeq.any isSeq ts && DotSeq.any isInd ts -> raise (MixedDataAndNestedSequences ts)
            | ts -> DotSeq.map typeKindExn ts |> maxKindsExn
        | TApp (l, r) -> applyKindExn (typeKindExn l) (typeKindExn r)
    
    let rec typeKindSubstExn subst t =
        match t with
        | TVar (v, k) -> TVar (v, kindSubst subst k)
        | TDotVar (v, k) -> TDotVar (v, kindSubst subst k)
        | TCon (c, k) -> TCon (c, kindSubst subst k)

        | TTrue k -> TTrue (kindSubst subst k)
        | TFalse k -> TFalse (kindSubst subst k)
        | TAnd (l, r) -> TAnd (typeKindSubstExn subst l, typeKindSubstExn subst r)
        | TOr (l, r) -> TOr (typeKindSubstExn subst l, typeKindSubstExn subst r)
        | TNot n -> TNot (typeKindSubstExn subst n)

        | TAbelianOne k -> TAbelianOne (kindSubst subst k)
        | TExponent (b, p) -> TExponent (typeKindSubstExn subst b, p)
        | TMultiply (l, r) -> TMultiply (typeKindSubstExn subst l, typeKindSubstExn subst r)

        | TRowExtend k -> TRowExtend (kindSubst subst k)
        | TEmptyRow k -> TEmptyRow (kindSubst subst k)

        | TSeq ts -> TSeq (DotSeq.map (typeKindSubstExn subst) ts)
        | TApp (l, r) -> TApp (typeKindSubstExn subst l, typeKindSubstExn subst r)
        | _ -> t


    /// Perform many basic simplification steps to minimize the Boolean equations in a type as much as possible, and minimize
    /// integer constants in fixed-size equation types.
    let rec simplifyType ty =
        let k = typeKindExn ty
        if isKindBoolean k
        then typeToBooleanEqn ty |> Boolean.minimize |> booleanEqnToType k
        elif k = KFixed
        then
            let eqn = typeToFixedEqn ty
            let simplified = Map.toSeq eqn.Constants |> Seq.sumBy (fun (b, e) -> b * e)
            fixedEqnToType (new Abelian.Equation<string, int>(eqn.Variables, if simplified = 0 then Map.empty else Map.empty.Add(simplified, 1)))
        else
            match ty with
            | TApp (l, r) -> typeApp (simplifyType l) (simplifyType r)
            | TSeq ts -> DotSeq.map simplifyType ts |> TSeq
            | b -> b

    let simplifyQual ty = { Context = ty.Context; Head = simplifyType ty.Head }


    // Substitution computations
    let zipExtendRest (ts : Type) =
        match ts with
        | TSeq (DotSeq.SInd (_, rs)) -> TSeq rs
        | TSeq (DotSeq.SDot (_, rs)) -> TSeq rs
        | TSeq (DotSeq.SEnd) -> failwith "Tried to zipExtendRest an empty sequence."
        | any -> any

    let zipExtendHeads (ts : Type) =
        match ts with
        | TSeq (DotSeq.SInd (b, _)) -> b
        | TSeq (DotSeq.SDot (b, _)) -> b
        | TSeq (DotSeq.SEnd) -> failwith "Tried to zipExtendHeads an empty sequence."
        | any -> any

    let rec dotOrInd (ts : DotSeq.DotSeq<Type>) =
        match ts with
        | DotSeq.SInd (TSeq (DotSeq.SDot _), _) -> DotSeq.SDot
        | DotSeq.SDot (TSeq (DotSeq.SDot _), _) -> DotSeq.SDot
        | DotSeq.SInd (_, rs) -> dotOrInd rs
        | DotSeq.SDot (_, rs) -> dotOrInd rs
        | DotSeq.SEnd -> DotSeq.SInd

    let rec spliceDots (ts : DotSeq.DotSeq<Type>) =
        match ts with
        | DotSeq.SDot (TSeq ts, rs) ->
            if DotSeq.any isSeq ts
            then DotSeq.SDot (TSeq ts, spliceDots rs)
            else DotSeq.append ts (spliceDots rs)
        | DotSeq.SDot (d, rs) -> DotSeq.SDot (d, spliceDots rs)
        | DotSeq.SInd (i, rs) -> DotSeq.SInd (i, spliceDots rs)
        | DotSeq.SEnd -> DotSeq.SEnd

    let rec zipExtend (ts : DotSeq.DotSeq<Type>) =
        let rec zipExtendInc ts =
            if DotSeq.any isSeq ts
            then if DotSeq.all emptySeqOrInd ts
                 then DotSeq.SEnd
                 else if DotSeq.any (fun t -> isSeq t && emptySeqOrInd t) ts
                 then failwith "zipExtend sequences were of different length."
                 else (dotOrInd ts) (TSeq (zipExtend (DotSeq.map zipExtendHeads ts)), zipExtendInc (DotSeq.map zipExtendRest ts))
            else ts

        if DotSeq.all isSeq ts && DotSeq.anyIndInSeq ts
        then DotSeq.map (getSeq >> zipExtend >> TSeq) ts
        else zipExtendInc (spliceDots ts)

    let rec fixApp (t : Type) =
        match t with
        | TApp (TSeq ls, TSeq rs) -> DotSeq.zipWith ls rs typeApp |> DotSeq.map fixApp |> TSeq
        | TApp (TSeq ls, r) -> DotSeq.zipWith ls (DotSeq.map (constant r) ls) typeApp |> DotSeq.map fixApp |> TSeq
        | TApp (l, TSeq rs) ->
            // special case for type constructors that take sequences as arguments: don't bubble last nested substitution sequence up!
            // instead, the constructor takes those most nested sequences as an argument
            let canApplySeq =
                match typeKindExn l with
                | KArrow (arg, _) -> arg = typeKindExn (TSeq rs)
                | _ -> false
            if canApplySeq
            then typeApp l (TSeq rs)
            else DotSeq.zipWith (DotSeq.map (constant l) rs) rs typeApp |> DotSeq.map fixApp |> TSeq
        | TApp _ -> t
        | _ -> invalidArg (nameof t) "Called fixApp on non TApp type"

    let rec fixAnd (t : Type) =
        match t with
        | TAnd (TSeq ls, TSeq rs) -> DotSeq.zipWith ls rs typeAnd |> DotSeq.map fixAnd |> TSeq
        | TAnd (TSeq ls, r) -> DotSeq.zipWith ls (DotSeq.map (constant r) ls) typeAnd |> DotSeq.map fixAnd |> TSeq
        | TAnd (l, TSeq rs) -> DotSeq.zipWith (DotSeq.map (constant l) rs) rs typeAnd |> DotSeq.map fixAnd |> TSeq
        | TAnd _ -> t
        | _ -> invalidArg (nameof t) "Called fixAnd on non TAnd type"

    let rec fixOr (t : Type) =
        match t with
        | TOr (TSeq ls, TSeq rs) -> DotSeq.zipWith ls rs typeOr |> DotSeq.map fixOr |> TSeq
        | TOr (TSeq ls, r) -> DotSeq.zipWith ls (DotSeq.map (constant r) ls) typeOr |> DotSeq.map fixOr |> TSeq
        | TOr (l, TSeq rs) -> DotSeq.zipWith (DotSeq.map (constant l) rs) rs typeOr |> DotSeq.map fixOr |> TSeq
        | TOr _ -> t
        | _ -> invalidArg (nameof t) "Called fixAnd on non TOr type"

    let rec fixNot (t : Type) =
        match t with
        | TNot (TSeq ns) -> DotSeq.map typeNot ns |> TSeq
        | TNot _ -> t
        | _ -> invalidArg (nameof t) "Called fixExp on non TExponent type"

    let rec fixExp (t : Type) =
        match t with
        | TExponent (TSeq bs, n) -> DotSeq.map (fun b -> typeExp b n) bs |> TSeq
        | TExponent _ -> t
        | _ -> invalidArg (nameof t) "Called fixExp on non TExponent type"

    let rec fixMul (t : Type) =
        match t with
        | TMultiply (TSeq ls, TSeq rs) -> DotSeq.zipWith ls rs typeMul |> DotSeq.map fixMul |> TSeq
        | TMultiply (TSeq ls, r) -> DotSeq.zipWith ls (DotSeq.map (constant r) ls) typeMul |> DotSeq.map fixMul |> TSeq
        | TMultiply (l, TSeq rs) -> DotSeq.zipWith (DotSeq.map (constant l) rs) rs typeMul |> DotSeq.map fixMul |> TSeq
        | TMultiply _ -> t
        | _ -> invalidArg (nameof t) "Called fixAnd on non TMultiply type"

    let rec seqToDisjunctions seq kind =
        match seq with
        | DotSeq.SEnd -> TFalse kind
        | DotSeq.SInd (e, DotSeq.SEnd) -> e
        | DotSeq.SDot (e, DotSeq.SEnd) -> e
        | DotSeq.SInd (e, ds) -> TOr (e, seqToDisjunctions ds kind)
        | DotSeq.SDot (e, ds) -> TOr (e, seqToDisjunctions ds kind)

    let rec lowestSequencesToDisjunctions kind sub =
        match sub with
        | TSeq ts when DotSeq.all isSeq ts -> DotSeq.map (lowestSequencesToDisjunctions kind) ts |> TSeq
        | TSeq ts -> seqToDisjunctions ts kind
        | _ -> sub

    let rec typeSubstExn subst target =
        match target with
        | TVar (n, _) -> if Map.containsKey n subst then subst.[n] else target
        // special case for handling dotted variables inside boolean equations, necessary for allowing polymorphic sharing of tuples based
        // on the sharing status of their elements (i.e. one unique element requires whole tuple to be unique)
        | TDotVar (n, k) ->
            if Map.containsKey n subst
            then lowestSequencesToDisjunctions k subst.[n]
            else target
        | TApp (l, r) -> 
            let lsub = typeSubstExn subst l
            TApp (lsub, typeSubstExn subst r) |> fixApp
        | TSeq ts ->
            let freeDotted = typeFree (TSeq (DotSeq.dotted ts))
            let overlapped = Set.intersect freeDotted (mapKeys subst)
            if not (Set.isEmpty overlapped) && Set.isProperSubset overlapped freeDotted
            then invalidOp $"Potentially unsound operation: trying to substitute for only some of the variables beneath a dot in a sequence: {subst} --> {TSeq ts}"
            else DotSeq.map (typeSubstExn subst) ts |> zipExtend |> TSeq
        | TAnd (l, r) -> TAnd (typeSubstExn subst l, typeSubstExn subst r) |> fixAnd
        | TOr (l, r) -> TOr (typeSubstExn subst l, typeSubstExn subst r) |> fixOr
        | TNot n -> TNot (typeSubstExn subst n) |> fixNot
        | TExponent (b, n) -> TExponent (typeSubstExn subst b, n) |> fixExp
        | TMultiply (l, r) -> TMultiply (typeSubstExn subst l, typeSubstExn subst r) |> fixMul
        | _ -> target

    let typeSubstSimplifyExn subst = typeSubstExn subst >> simplifyType

    let rec predSubstExn subst pred = { pred with Argument = typeSubstExn subst pred.Argument }

    let applySubstContextExn subst context = List.map (predSubstExn subst) context
    
    let qualSubstExn subst qual = { Context = applySubstContextExn subst qual.Context; Head = typeSubstExn subst qual.Head }

    let composeSubstExn = composeSubst typeSubstSimplifyExn
    
    let mergeSubstExn (s1 : Map<string, Type>) (s2 : Map<string, Type>) =
        let agree = Set.forall (fun v -> s1.[v] = s2.[v]) (Set.intersect (mapKeys s1) (mapKeys s2))
        if agree then mapUnion fst s1 s2 else invalidOp "Substitutions could not be merged"


    // Fresh types
    let freshTypeExn (fresh : FreshVars) quantified body =
        let fresh = fresh.FreshN "f" (Seq.length quantified)
        let freshVars = Seq.zip fresh (List.map snd quantified) |> Seq.map TVar
        let freshened = Seq.zip (List.map fst quantified) freshVars |> Map.ofSeq
        typeSubstExn freshened body

    let freshQualExn (fresh : FreshVars) quantified qual =
        let fresh = fresh.FreshN "f" (Seq.length quantified)
        let freshVars = Seq.zip fresh (List.map snd quantified) |> Seq.map TVar
        let freshened = Seq.zip (List.map fst quantified) freshVars |> Map.ofSeq
        qualSubstExn freshened qual

    let instantiateExn fresh scheme = freshQualExn fresh scheme.Quantified scheme.Body