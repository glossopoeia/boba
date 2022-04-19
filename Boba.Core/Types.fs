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

    let integerSizeFnSuffix intSize = intSize.ToString().ToLower()

    /// Rather than duplicating a lot of different constructors throughout the pipeline, we enumerate the separate sizes of floats
    /// here for re-use. Floating-point numbers are mostly treated the same other than their size.
    [<DebuggerDisplay("{ToString()}")>]
    type FloatSize =
        | Single
        | Double

    let floatSizeFnSuffix floatSize = floatSize.ToString().ToLower()


    /// It is convenient throughout the implementation of the type system to be able to pattern match on some primitive type
    /// constructors. Using the standard type constructor, and making the primitives constants, would result in pattern matching
    /// on the string name of the primitive, which is bug prone and far less maintainable. However, we don't want to clutter the
    /// Type data structure with noisy type constants, so the primitives have been separated out here.
    [<DebuggerDisplay("{ToString()}")>]
    type PrimType =
        /// Function types in Boba can be 'qualified' by a set of constraints. These constraints help
        /// to drive type inference and allow a powerful form of ad-hoc polymorphism, similar to
        /// Haskell's typeclass constraints. This constructor allows us to represent qualified types
        /// as just another form of type, but PrQual should really only occur as an outermost type
        /// constructor since it doesn't make a lot of sense for constraints to be nested in types.
        | PrQual
        /// Since Boba supports a form of variable-arity polymorphism, we also need to have tuples
        /// of constraints, which can be variable-arity. This allows for things like a generic
        /// tuple equality function supporting variable arity polymorphism.
        | PrConstraintTuple
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
        | PrString
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
            | PrQual -> "Qual"
            | PrConstraintTuple -> "Constraints"
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
            | PrString -> "String"
            | PrInteger k -> $"{k}"
            | PrFloat k -> $"{k}"

    let primKind prim =
        match prim with
        | PrQual -> karrow KConstraint (karrow KValue KValue)
        | PrConstraintTuple -> karrow (kseq KConstraint) KConstraint
        | PrValue -> karrow KData (karrow KSharing KValue)
        | PrBool -> KData
        | PrInteger _ -> karrow KUnit KData
        | PrFloat _ -> karrow KUnit KData
        | PrString -> karrow KTrust (karrow KClearance KData)
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

        /// Kind argument here is not the kind of the constructor, but the non-sequence base kind at the bottom of the nested sequence kinds.
        | TSeq of seq: DotSeq.DotSeq<Type> * kind: Kind
        | TApp of cons: Type * arg: Type
        override this.ToString () =
            match this with
            | TVar (n, _) -> $"{n}"
            | TDotVar (n, _) -> $"{n}..."
            | TCon (n, _) -> n
            | TPtr n -> $"ptr<{n}>"
            | TPrim n -> $"{n}"
            | TTrue KSharing -> "*"
            | TFalse KSharing -> "***"
            | TTrue KTotality -> "■"
            | TFalse KTotality -> "□"
            | TTrue KTrust -> "trusted"
            | TFalse KTrust -> "untrusted"
            | TTrue KClearance -> "secret"
            | TFalse KClearance -> "clear"
            | TTrue _ -> "true?"
            | TFalse _ -> "false?"
            | TAnd (l, r) -> $"({l} ∧ {r})"
            | TOr (l, r) -> $"({l} ∨ {r})"
            | TNot b -> $"!{b}"
            | TAbelianOne _ -> ""
            | TExponent (b, p) -> $"{b}^{p}"
            | TMultiply (l, r) -> $"({l}{r})"
            | TFixedConst n -> $"{n}"
            | TRowExtend _ -> "rowCons"
            | TEmptyRow _ -> "."
            | TSeq (ts, _) -> $"{DotSeq.revString ts}"
            | TApp (TApp (TPrim PrQual, TApp (TPrim PrConstraintTuple, TSeq (DotSeq.SEnd, KConstraint))), fn) -> $"{fn}"
            | TApp (TApp (TPrim PrQual, cnstrs), fn) -> $"{cnstrs} => {fn}"
            | TApp (TApp (TApp (TApp (TApp (TPrim PrFunction, e), p), t), i), o) ->
                $"{i} ==[{e}][{p}][{t}]==> {o}"
            | TApp (TApp (TPrim PrValue, (TApp _ as d)), TTrue KSharing) -> $"({d})*"
            | TApp (TApp (TPrim PrValue, (TApp _ as d)), TFalse KSharing) -> $"({d})***"
            | TApp (TApp (TPrim PrValue, (TApp _ as d)), s) -> $"({d})^{s}"
            | TApp (TApp (TPrim PrValue, d), TTrue KSharing) -> $"{d}*"
            | TApp (TApp (TPrim PrValue, d), TFalse KSharing) -> $"{d}***"
            | TApp (TApp (TPrim PrValue, d), s) -> $"{d}^{s}"
            | TApp (l, (TApp (TApp (TPrim PrValue, _), _) as r)) -> $"{l} {r}"
            | TApp (l, (TApp _ as r)) -> $"{l} ({r})"
            | TApp (l, r) -> $"{l} {r}"

    type TypeScheme =
        { Quantified: List<(string * Kind)>; Body: Type }
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
        | TSeq (ts, _) -> ts
        | _ -> failwith "Called getSeq on non-TSeq"

    let emptySeqOrInd (t : Type) =
        match t with
        | TSeq (DotSeq.SEnd, _) -> true
        | TSeq _ -> false
        | _ -> true


    // Functional constructors
    let trustedAttr = TTrue KTrust
    let untrustedAttr = TFalse KTrust
    let totalAttr = TTrue KTotality
    let partialAttr = TFalse KTotality
    let uniqueAttr = TTrue KSharing
    let sharedAttr = TFalse KSharing
    let clearAttr = TTrue KClearance
    let secretAttr = TFalse KClearance

    let isTypeVar ty =
        match ty with
        | TVar (_, _) -> true
        | _ -> false

    let typeVar name kind = TVar (name, kind)
    let typeDotVar name kind = TDotVar (name, kind)
    let typeVarToDotVar tv =
        let (TVar (name, kind)) = tv
        TDotVar (name, kind)
    let typeCon name kind = TCon (name, kind)
    let typeApp cons arg = TApp (cons, arg)
    let typeSeq seq kind = TSeq (seq, kind)

    let typeNot n =
        match n with
        | TNot b -> b
        | _ -> TNot n
    let typeOr l r =
        match l, r with
        | TTrue k, _ -> TTrue k
        | _, TTrue k -> TTrue k
        | TFalse _, r -> r
        | l, TFalse _ -> l
        | _ -> TOr (l, r)
    let typeAnd l r =
        match l, r with
        | TFalse k, _ -> TFalse k
        | _, TFalse k -> TFalse k
        | TTrue _, r -> r
        | l, TTrue _ -> l
        | _ -> TAnd (l, r)

    let typeExp b n =
        match b with
        //| TExponent (b2, n2) -> TExponent (b2, n * n2)
        //| _ when n = 1 -> b
        | _ -> TExponent (b, n)
    let typeMul l r =
        match l, r with
        | TAbelianOne _, _ -> r
        | _, TAbelianOne _ -> l
        | _ -> TMultiply (l, r)

    let typeValueSeq seq = typeSeq seq KValue

    let typeConstraintSeq seq = typeSeq seq KConstraint

    let typeField name ty = typeApp (typeCon name (karrow KValue KField)) ty

    /// Creates a qualified type with the given context sequence.
    let qualType context head =
        typeApp
            (typeApp
                (TPrim PrQual)
                (typeApp (TPrim PrConstraintTuple) (TSeq (context, KConstraint))))
            head

    /// Creates a qualified type with an empty context.
    let unqualType head = qualType DotSeq.SEnd head

    /// Extracts the context and head of a qualified type.
    let qualTypeComponents ty =
        match ty with
        | TApp (TApp (TPrim PrQual, TApp (TPrim PrConstraintTuple, TSeq (context, KConstraint))), head) -> context, head
        | _ -> failwith $"Expected a qualified type form, got ${ty}"

    /// Extracts the context of a qualified type.
    let qualTypeContext = qualTypeComponents >> fst

    /// Extracts the head of a qualified type.
    let qualTypeHead = qualTypeComponents >> snd

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
        | Boolean.BAnd (l, r) -> typeAnd (booleanEqnToType kind l) (booleanEqnToType kind r)
        | Boolean.BOr (l, r) -> typeOr (booleanEqnToType kind l) (booleanEqnToType kind r)
        | Boolean.BNot n -> typeNot (booleanEqnToType kind n)
    
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
        | _ -> failwith $"Tried to convert a non-row type {ty} to a field row."

    let rec rowToType row =
        match row.Elements with
        | e :: es ->
            typeApp (typeApp (TRowExtend row.ElementKind) e) (rowToType { row with Elements = es })
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
        | TSeq (ts, k) -> DotSeq.toList ts |> List.map typeFreeWithKinds |> Set.unionMany
        | TApp (l, r) -> Set.union (typeFreeWithKinds l) (typeFreeWithKinds r)

        | TAnd (l, r) -> Set.union (typeFreeWithKinds l) (typeFreeWithKinds r)
        | TOr (l, r) -> Set.union (typeFreeWithKinds l) (typeFreeWithKinds r)
        | TNot n -> typeFreeWithKinds n

        | TExponent (b, _) -> typeFreeWithKinds b
        | TMultiply (l, r) -> Set.union (typeFreeWithKinds l) (typeFreeWithKinds r)

        | _ -> Set.empty

    let typeFree = typeFreeWithKinds >> Set.map fst

    let schemeFree s = Set.difference (typeFree s.Body) (Set.ofList (List.map fst s.Quantified))


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

        | TSeq (ts, k) ->
            match ts with
            | ts when DotSeq.all isInd ts -> KSeq k
            | ts when DotSeq.any isSeq ts && DotSeq.any isInd ts -> raise (MixedDataAndNestedSequences ts)
            | ts -> DotSeq.map typeKindExn ts |> maxKindsExn
        | TApp (l, r) -> applyKindExn (typeKindExn l) (typeKindExn r)
    
    let isTypeWellKinded ty =
        try
            let k = typeKindExn ty
            true
        with
            | ex -> false
    
    let rec typeKindSubstExn subst t =
        match t with
        | TVar (v, k) -> TVar (v, kindSubst subst k)
        | TDotVar (v, k) -> TDotVar (v, kindSubst subst k)
        | TCon (c, k) -> TCon (c, kindSubst subst k)

        | TTrue k -> TTrue (kindSubst subst k)
        | TFalse k -> TFalse (kindSubst subst k)
        | TAnd (l, r) -> typeAnd (typeKindSubstExn subst l) (typeKindSubstExn subst r)
        | TOr (l, r) -> typeOr (typeKindSubstExn subst l) (typeKindSubstExn subst r)
        | TNot n -> typeNot (typeKindSubstExn subst n)

        | TAbelianOne k -> TAbelianOne (kindSubst subst k)
        | TExponent (b, p) -> TExponent (typeKindSubstExn subst b, p)
        | TMultiply (l, r) -> TMultiply (typeKindSubstExn subst l, typeKindSubstExn subst r)

        | TRowExtend k -> TRowExtend (kindSubst subst k)
        | TEmptyRow k -> TEmptyRow (kindSubst subst k)

        | TSeq (ts, k) -> TSeq (DotSeq.map (typeKindSubstExn subst) ts, k)
        | TApp (l, r) -> TApp (typeKindSubstExn subst l, typeKindSubstExn subst r)
        | _ -> t


    /// Perform many basic simplification steps to minimize the Boolean equations, fixed-size type expressions,
    /// and non-scoped labeled rows.
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
            | TSeq (ts, k) -> TSeq (DotSeq.map simplifyType ts, k)
            | b -> b


    // Substitution computations


    let zipExtendRest (ts : Type) =
        match ts with
        | TSeq (DotSeq.SInd (_, rs), k) -> TSeq (rs, k)
        | TSeq (DotSeq.SDot (_, rs), k) -> TSeq (rs, k)
        | TSeq (DotSeq.SEnd, _) -> failwith "Tried to zipExtendRest an empty sequence."
        | any -> any

    let zipExtendHeads (ts : Type) =
        match ts with
        | TSeq (DotSeq.SInd (b, _), _) -> b
        | TSeq (DotSeq.SDot (b, _), _) -> b
        | TSeq (DotSeq.SEnd, _) -> failwith "Tried to zipExtendHeads an empty sequence."
        | any -> any

    let rec dotOrInd (ts : DotSeq.DotSeq<Type>) =
        match ts with
        | DotSeq.SInd (TSeq (DotSeq.SDot _, _), _) -> DotSeq.SDot
        | DotSeq.SDot (TSeq (DotSeq.SDot _, _), _) -> DotSeq.SDot
        | DotSeq.SInd (_, rs) -> dotOrInd rs
        | DotSeq.SDot (_, rs) -> dotOrInd rs
        | DotSeq.SEnd -> DotSeq.SInd

    /// Given a sequence of a form like `<a, <b*>..., c>`, where `b*` does not contain any subsequences,
    /// returns a sequence of the form `<a, b*, c>`. Abstractly, if the examined sequence contains any dotted
    /// subsequences which themselves contain no subsequences, then the dotted subsequences have their elements
    /// inserted in-order into the examined sequence at the position of the dotted subsequence.
    let rec spliceDots (ts : DotSeq.DotSeq<Type>) =
        match ts with
        | DotSeq.SDot (TSeq (ts, k), rs) ->
            if DotSeq.any isSeq ts
            then DotSeq.SDot (TSeq (ts, k), spliceDots rs)
            else DotSeq.append ts (spliceDots rs)
        | DotSeq.SDot (d, rs) -> DotSeq.SDot (d, spliceDots rs)
        | DotSeq.SInd (i, rs) -> DotSeq.SInd (i, spliceDots rs)
        | DotSeq.SEnd -> DotSeq.SEnd

    let rec zipExtend k (ts : DotSeq.DotSeq<Type>) =
        let rec zipExtendInc ts =
            if DotSeq.any isSeq ts
            then if DotSeq.all emptySeqOrInd ts
                 then DotSeq.SEnd
                 else if DotSeq.any (fun t -> isSeq t && emptySeqOrInd t) ts
                 then failwith "zipExtend sequences were of different length."
                 else (dotOrInd ts) (TSeq (zipExtend k (DotSeq.map zipExtendHeads ts), k), zipExtendInc (DotSeq.map zipExtendRest ts))
            else ts

        if DotSeq.all isSeq ts && DotSeq.anyIndInSeq ts
        then DotSeq.map (fun t -> TSeq (getSeq t |> zipExtend k, k)) ts
        else zipExtendInc (spliceDots ts)

    let rec fixApp (t : Type) =
        match t with
        | TApp (TSeq (ls, lk), TSeq (rs, rk)) when lk = rk ->
            TSeq (DotSeq.zipWith ls rs typeApp |> DotSeq.map fixApp, lk)
        | TApp (TSeq (ls, lk), TSeq (rs, rk)) when lk <> rk ->
            invalidOp $"Tried to fixApp on sequences with different kinds: {lk}, {rk}"
        | TApp (TSeq (ls, k), r) ->
            TSeq (DotSeq.zipWith ls (DotSeq.map (constant r) ls) typeApp |> DotSeq.map fixApp, k)
        | TApp (l, TSeq (rs, k)) ->
            // special case for type constructors that take sequences as arguments: don't bubble last nested substitution sequence up!
            // instead, the constructor takes those most nested sequences as an argument
            let canApplySeq =
                match typeKindExn l with
                | KArrow (arg, _) -> arg = typeKindExn (TSeq (rs, k))
                | _ -> false
            if canApplySeq
            then typeApp l (TSeq (rs, k))
            else TSeq (DotSeq.zipWith (DotSeq.map (constant l) rs) rs typeApp |> DotSeq.map fixApp, k)
        | TApp _ -> t
        | _ -> invalidArg (nameof t) "Called fixApp on non TApp type"

    let rec fixAnd (t : Type) =
        match t with
        | TAnd (TFalse k, _) -> TFalse k
        | TAnd (_, TFalse k) -> TFalse k
        | TAnd (TTrue _, r) -> r
        | TAnd (l, TTrue _) -> l
        | TAnd (TSeq (ls, lk), TSeq (rs, rk)) when lk = rk ->
            TSeq (DotSeq.zipWith ls rs typeAnd |> DotSeq.map fixAnd, lk)
        | TAnd (TSeq (ls, lk), TSeq (rs, rk)) when lk <> rk ->
            invalidOp $"Tried to fixAnd on sequences with different kinds: {lk}, {rk}"
        | TAnd (TSeq (ls, k), r) ->
            TSeq (DotSeq.zipWith ls (DotSeq.map (constant r) ls) typeAnd |> DotSeq.map fixAnd, k)
        | TAnd (l, TSeq (rs, k)) ->
            TSeq (DotSeq.zipWith (DotSeq.map (constant l) rs) rs typeAnd |> DotSeq.map fixAnd, k)
        | TAnd _ -> t
        | _ -> invalidArg (nameof t) "Called fixAnd on non TAnd type"

    let rec fixOr (t : Type) =
        match t with
        | TOr (TTrue k, _) -> TTrue k
        | TOr (_, TTrue k) -> TTrue k
        | TOr (TFalse _, r) -> r
        | TOr (l, TFalse _) -> l
        | TOr (TSeq (ls, lk), TSeq (rs, rk)) when lk = rk ->
            TSeq (DotSeq.zipWith ls rs typeOr |> DotSeq.map fixOr, lk)
        | TOr (TSeq (ls, lk), TSeq (rs, rk)) when lk <> rk ->
            invalidOp $"Tried to fixOr on sequences with different kinds: {lk}, {rk}"
        | TOr (TSeq (ls, k), r) ->
            TSeq (DotSeq.zipWith ls (DotSeq.map (constant r) ls) typeOr |> DotSeq.map fixOr, k)
        | TOr (l, TSeq (rs, k)) ->
            TSeq (DotSeq.zipWith (DotSeq.map (constant l) rs) rs typeOr |> DotSeq.map fixOr, k)
        | TOr _ -> t
        | _ -> invalidArg (nameof t) "Called fixOr on non TOr type"

    let rec fixNot (t : Type) =
        match t with
        | TNot (TSeq (ns, k)) -> TSeq (DotSeq.map typeNot ns, k)
        | TNot _ -> t
        | _ -> invalidArg (nameof t) "Called fixNot on non TExponent type"

    let rec fixExp (t : Type) =
        match t with
        | TExponent (TSeq (bs, k), n) -> TSeq (DotSeq.map (fun b -> typeExp b n) bs, k)
        | TExponent _ -> t
        | _ -> invalidArg (nameof t) "Called fixExp on non TExponent type"

    let rec fixMul (t : Type) =
        match t with
        | TMultiply (TSeq (ls, lk), TSeq (rs, rk)) when lk = rk ->
            TSeq (DotSeq.zipWith ls rs typeMul |> DotSeq.map fixMul, lk)
        | TMultiply (TSeq (ls, lk), TSeq (rs, rk)) when lk <> rk ->
            invalidOp $"Tried to fixMul on sequences with different kinds: {lk}, {rk}"
        | TMultiply (TSeq (ls, k), r) ->
            TSeq (DotSeq.zipWith ls (DotSeq.map (constant r) ls) typeMul |> DotSeq.map fixMul, k)
        | TMultiply (l, TSeq (rs, k)) ->
            TSeq (DotSeq.zipWith (DotSeq.map (constant l) rs) rs typeMul |> DotSeq.map fixMul, k)
        | TMultiply _ -> t
        | _ -> invalidArg (nameof t) "Called fixMul on non TMultiply type"

    let rec seqToDisjunctions seq kind =
        match seq with
        | DotSeq.SEnd -> TFalse kind
        | DotSeq.SInd (e, DotSeq.SEnd) -> e
        | DotSeq.SDot (e, DotSeq.SEnd) -> e
        | DotSeq.SInd (e, ds) -> TOr (e, seqToDisjunctions ds kind)
        | DotSeq.SDot (e, ds) -> TOr (e, seqToDisjunctions ds kind)

    /// Helper function for converting an extended sequence to a Boolean disjunction. This is primarily useful
    /// for helping determine the sharing attribute of a tuple, which in the type of `fst` is something like
    /// `fst : (a ^ s, z ^ r ...) ^ (s or r... or t) -> a ^ s`
    let rec lowestSequencesToDisjunctions kind sub =
        match sub with
        | TSeq (DotSeq.SEnd, k) -> TFalse kind
        | TSeq (ts, k) when DotSeq.all isSeq ts -> TSeq (DotSeq.map (lowestSequencesToDisjunctions kind) ts, k)
        | TSeq (ts, _) -> seqToDisjunctions ts kind
        | _ -> sub

    let rec typeSubstExn subst target =
        match target with
        | TVar (n, _) -> if Map.containsKey n subst then subst.[n] else target
        // special case for handling dotted variables inside boolean equations, necessary for allowing polymorphic sharing of tuples based
        // on the sharing status of their elements (i.e. one unique element requires whole tuple to be unique)
        | TDotVar (n, k) ->
            if Map.containsKey n subst
            then
                match subst.[n] with
                | TSeq _ -> lowestSequencesToDisjunctions k subst.[n]
                | TVar (v, k) -> TDotVar (v, k)
                | _ -> failwith $"Trying to substitute a dotted Boolean var with something unexpected: {subst.[n]}"
            else target
        | TApp (l, r) -> 
            let lsub = typeSubstExn subst l
            TApp (lsub, typeSubstExn subst r) |> fixApp
        | TSeq (ts, k) ->
            //let freeDotted = typeFree (TSeq (DotSeq.dotted ts, k))
            //let overlapped = Set.intersect freeDotted (mapKeys subst)
            //if not (Set.isEmpty overlapped) && Set.isProperSubset overlapped freeDotted
            //then
            //    invalidOp $"Potentially unsound operation: trying to substitute for only some of the variables beneath a dot in a sequence: {subst} --> {TSeq (ts, k)}"
            //else
            TSeq (DotSeq.map (typeSubstExn subst) ts |> zipExtend k, k)
        | TAnd (l, r) -> TAnd (typeSubstExn subst l, typeSubstExn subst r) |> fixAnd
        | TOr (l, r) -> TOr (typeSubstExn subst l, typeSubstExn subst r) |> fixOr
        | TNot n -> TNot (typeSubstExn subst n) |> fixNot
        | TExponent (b, n) -> TExponent (typeSubstExn subst b, n) |> fixExp
        | TMultiply (l, r) -> TMultiply (typeSubstExn subst l, typeSubstExn subst r) |> fixMul
        | _ -> target

    let typeSubstSimplifyExn subst = typeSubstExn subst >> simplifyType

    let composeSubstExn = composeSubst typeSubstSimplifyExn
    
    let mergeSubstExn (s1 : Map<string, Type>) (s2 : Map<string, Type>) =
        let elemAgree v =
            if isKindBoolean (typeKindExn s1.[v])
            // TODO: is this actually safe? Boolean matching seems to cause problems here
            then true
            elif s1.[v] = s2.[v]
            then true
            else invalidOp $"Match substitutions clashed at {v}: {s1.[v]} <> {s2.[v]}"
        let agree = Set.forall (fun v -> elemAgree v) (Set.intersect (mapKeys s1) (mapKeys s2))
        if agree then mapUnion fst s1 s2 else invalidOp "Substitutions could not be merged"


    // Fresh types
    let freshTypeExn (fresh : FreshVars) quantified body =
        let fresh = fresh.FreshN "f" (Seq.length quantified)
        let freshVars = Seq.zip fresh (Seq.map snd quantified) |> Seq.map TVar
        let freshened = Seq.zip (Seq.map fst quantified) freshVars |> Map.ofSeq
        typeSubstExn freshened body

    let instantiateExn fresh scheme = freshTypeExn fresh scheme.Quantified scheme.Body