namespace Boba.Core

module Types =

    open System.Diagnostics
    open Common
    open Fresh
    open Kinds

    /// Rather than duplicating a lot of different constructors throughout the pipeline,
    /// we enumerate the separate sizes of integers here for re-use. Integers are mostly
    /// treated the same other than their size.
    type IntegerSize =
        | I8 | U8
        | I16 | U16
        | I32 | U32
        | I64 | U64
        | INative | UNative

    /// Rather than duplicating a lot of different constructors throughout the pipeline,
    /// we enumerate the separate sizes of floats here for re-use. Floating-point numbers
    /// are mostly treated the same other than their size.
    [<DebuggerDisplay("{ToString()}")>]
    type FloatSize =
        | Single
        | Double


    [<Literal>]
    let PrimFunctionCtorName = "Function"
    [<Literal>]
    let PrimTrackedCtorName = "Tracked"
    [<Literal>]
    let PrimConstrainedCtorName = "Constrained"
    [<Literal>]
    let PrimConstraintTupleCtorName = "ConstraintTuple"
    [<Literal>]
    let primListCtorName = "List"
    [<Literal>]
    let primTupleCtorName = "Tuple"
    [<Literal>]
    let primRecordCtorName = "Record"
    [<Literal>]
    let primVariantCtorName = "Variant"    

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
        | TWildcard of kind: Kind
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
        | TSeq of seq: DotSeq.DotSeq<Type>
        | TApp of cons: Type * arg: Type
        override this.ToString () =
            match this with
            | TWildcard _ -> "_"
            | TVar (n, KRow _) -> $"{n}..."
            | TVar (n, k) -> $"{n}"
            | TDotVar (n, _) -> $"{n}..."
            | TCon (n, k) -> $"{n}"
            | TTrue _ -> "True"
            | TFalse _ -> "False"
            | TAnd (l, r) -> $"({l} && {r})"
            | TOr (l, r) -> $"({l} || {r})"
            | TNot b -> $"!{b}"
            | TAbelianOne _ -> "one"
            | TExponent (b, p) -> $"{b}^{p}"
            | TMultiply (l, r) -> $"({l}*{r})"
            | TFixedConst n -> $"{n}"
            | TRowExtend _ -> "rowCons"
            | TEmptyRow _ -> "."
            | TSeq ts -> $"<{DotSeq.revString ts}>"
            | TApp (TApp (TRowExtend _, e), TVar (v, _)) -> $"{v}..., {e}"
            | TApp (TApp (TRowExtend _, e), r) -> $"{r}, {e}"
            | TApp (
                TApp (TCon (PrimConstrainedCtorName, _),
                TApp (TCon (PrimConstraintTupleCtorName, _), TSeq DotSeq.SEnd)), fn) ->
                $" => {fn}"
            | TApp (
                TApp (TCon (PrimConstrainedCtorName, _),
                TApp (TCon (PrimConstraintTupleCtorName, _), TSeq cnstrs)), fn) ->
                $"{cnstrs} => {fn}"
            | TApp (TApp (TApp (TApp (TApp (TCon (PrimFunctionCtorName, _), e), p), t), i), o) ->
                $"{i} ===[ {e} ][ {p} ][ {t} ]==> {o}"
            | TApp (TApp (TCon (PrimTrackedCtorName, _), (TApp _ as d)), s) -> $"({d})^{s}"
            | TApp (TApp (TCon (PrimTrackedCtorName, _), d), s) -> $"{d}^{s}"
            | TApp (l, (TApp (TApp (TCon (PrimTrackedCtorName, _), _), _) as r)) -> $"{l} {r}"
            | TApp (l, (TApp _ as r)) -> $"{l} ({r})"
            | TApp (l, r) -> $"{l} {r}"

    type TypeScheme =
        { QuantifiedKinds: List<string>; QuantifiedTypes: List<(string * Kind)>; Body: Type }
        override this.ToString() = $"{this.Body}"

    type RowType = { Elements: List<Type>; RowEnd: Option<string>; ElementKind: Kind }

    /// The function type in Boba carries a lot more information than just inputs and outputs.
    /// It also tells what 'effects' it performs, what 'permissions' it requires from the context
    /// it runs in, and whether or not the compiler believes it is 'total'. All three of these attributes
    /// depend on the operations used within the body of the function, and can be inferred during
    /// type inference.
    let primFuctionCtor = 
        TCon (
            PrimFunctionCtorName,
            karrow (krow primEffectKind)
                (karrow (krow primPermissionKind)
                    (karrow primTotalityKind
                        (karrow (kseq primValueKind)
                            (karrow (kseq primValueKind) primDataKind)))))
    /// A tracked value is a data type with a sharing and validity annotation applied to it.
    /// Since sharing analysis is so viral, value-kinded types end up being the arguments
    /// required by most other types, since in Boba a data type without a sharing annotation
    /// cannot be inhabited by any values.
    let primTrackedCtor =
        TCon (PrimTrackedCtorName, karrow primDataKind (karrow primSharingKind primValueKind))
    /// Since Boba supports a form of variable-arity polymorphism, we also need to have tuples
    /// of constraints, which can be variable-arity. This allows for things like a generic
    /// tuple equality function supporting variable arity polymorphism.
    let primConstraintTupleCtor =
        TCon (PrimConstraintTupleCtorName, karrow (kseq primConstraintKind) primConstraintKind)
    /// Function types in Boba can be 'qualified' by a set of constraints. These constraints help
    /// to drive type inference and allow a powerful form of ad-hoc polymorphism, similar to
    /// Haskell's typeclass constraints. This constructor allows us to represent qualified types
    /// as just another form of type, but PrQual should really only occur as an outermost type
    /// constructor since it doesn't make a lot of sense for constraints to be nested in types.
    let primConstrainedCtor =
        TCon (PrimConstrainedCtorName, karrow primConstraintKind (karrow primValueKind primValueKind))
    let primBoolType = TCon ("Bool", primDataKind)
    let primNumericCtor size = TCon (size.ToString(), karrow primMeasureKind primDataKind)
    let primRuneCtor = TCon ("Rune", karrow primTrustKind (karrow primClearanceKind primDataKind))
    let primStringCtor = TCon ("String", karrow primTrustKind (karrow primClearanceKind primDataKind))
    let primRefCtor = TCon ("Ref", karrow primHeapKind (karrow primValueKind primDataKind))
    let primNurseryCtor = TCon ("Nursery", karrow primHeapKind primDataKind)
    let primCancelTokenCtor = TCon ("CancelToken", primDataKind)
    let primStateCtor = TCon ("st!", karrow primHeapKind primEffectKind)
    let primIterCtor = TCon ("iter!", karrow primValueKind primEffectKind)
    let primListCtor = TCon (primListCtorName, karrow primValueKind primDataKind)
    let primTupleCtor = TCon (primTupleCtorName, karrow (kseq primValueKind) primDataKind)
    let primRecordCtor = TCon (primRecordCtorName, karrow (krow primFieldKind) primDataKind)
    let primVariantCtor = TCon (primVariantCtorName, karrow (krow primFieldKind) primDataKind)


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
        | TSeq DotSeq.SEnd -> true
        | TSeq _ -> false
        | _ -> true


    // Functional constructors
    let trustedAttr = TTrue primTrustKind
    let untrustedAttr = TFalse primTrustKind
    let totalAttr = TTrue primTotalityKind
    let partialAttr = TFalse primTotalityKind
    let uniqueAttr = TTrue primSharingKind
    let sharedAttr = TFalse primSharingKind
    let clearAttr = TTrue primClearanceKind
    let secretAttr = TFalse primClearanceKind

    let isTypeVar ty =
        match ty with
        | TVar _ -> true
        | _ -> false

    let typeVar name kind = TVar (name, kind)
    let typeDotVar name kind = TDotVar (name, kind)
    let typeVarToDotVar tv =
        let (TVar (name, kind)) = tv
        TDotVar (name, kind)
    let typeCon name kind = TCon (name, kind)
    let typeApp cons arg = TApp (cons, arg)
    let typeSeq seq = TSeq seq

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
        | _ when n = 1 -> b
        | _ -> TExponent (b, n)
    let typeMul l r =
        match l, r with
        | TAbelianOne _, _ -> r
        | _, TAbelianOne _ -> l
        | _ -> TMultiply (l, r)

    let typeField name ty = typeApp (typeCon name (karrow primValueKind primFieldKind)) ty

    /// Creates a qualified type with the given context sequence.
    let qualType context head =
        typeApp
            (typeApp
                primConstrainedCtor
                (typeApp primConstraintTupleCtor (typeSeq context)))
            head

    /// Creates a qualified type with an empty context.
    let unqualType head = qualType DotSeq.SEnd head

    /// Extracts the context and head of a qualified type.
    let qualTypeComponents ty =
        match ty with
        | TApp (TApp (TCon (PrimConstrainedCtorName, _), TApp (TCon (PrimConstraintTupleCtorName, _), TSeq context)), head) -> context, head
        | _ -> failwith $"Expected a qualified type form, got {ty}"

    /// Extracts the context of a qualified type.
    let qualTypeContext = qualTypeComponents >> fst

    /// Extracts the head of a qualified type.
    let qualTypeHead = qualTypeComponents >> snd

    let isQualType ty =
        match ty with
        | TApp (TApp (TCon (PrimConstrainedCtorName, _), TApp (TCon (PrimConstraintTupleCtorName, _), TSeq _)), _) -> true
        | _ -> false

    let schemeType quantifiedKinds quantifiedTypes body =
        { QuantifiedKinds = quantifiedKinds; QuantifiedTypes = quantifiedTypes; Body = body }

    let rec typeToBooleanEqn ty =
        match ty with
        | TTrue _ -> Boolean.BTrue
        | TFalse _ -> Boolean.BFalse
        | TVar (n, k) when isKindBoolean k -> Boolean.BVar n
        | TDotVar (n, k) when isKindBoolean k -> Boolean.BDotVar n
        | TAnd (l, r) -> Boolean.BAnd (typeToBooleanEqn l, typeToBooleanEqn r)
        | TOr (l, r) -> Boolean.BOr (typeToBooleanEqn l, typeToBooleanEqn r)
        | TNot n -> Boolean.BNot (typeToBooleanEqn n)
        | _ -> failwith $"Tried to convert a non-Boolean type {ty} to a Boolean equation"

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

    let rec abelianEqnToType k (eqn : Abelian.Equation<string, string>) =
        typeMul
            (Map.fold (fun ty var exp -> typeMul ty (typeExp (typeVar var k) exp)) (TAbelianOne k) eqn.Variables)
            (Map.fold (fun ty unit exp -> typeMul ty (typeExp (typeCon unit k) exp)) (TAbelianOne k) eqn.Constants)

    let rec typeToUnitEqn ty =
        match ty with
        | TAbelianOne _ -> new Abelian.Equation<string, string>()
        | TVar (n, k) when isKindAbelian k -> new Abelian.Equation<string, string>(n)
        | TCon (n, k) when isKindAbelian k -> new Abelian.Equation<string, string>(Map.empty, Map.add n 1 Map.empty)
        | TMultiply (l, r) -> (typeToUnitEqn l).Add(typeToUnitEqn r)
        | TExponent (b, n) -> (typeToUnitEqn b).Scale(n)
        | _ -> failwith "Tried to convert a non-Abelian type to a unit equation"

    let rec fixedEqnToType (eqn: Abelian.Equation<string, int>) =
        typeMul
            (Map.fold (fun ty var exp -> typeMul ty (typeExp (typeVar var primFixedKind) exp)) (TFixedConst 0) eqn.Variables)
            (Map.fold (fun ty fix exp -> typeMul ty (typeExp (TFixedConst fix) exp)) (TFixedConst 0) eqn.Constants)

    let rec typeToFixedEqn ty =
        match ty with
        | TVar (n, k) when isKindAbelian k -> new Abelian.Equation<string, int>(n)
        | TFixedConst 0 -> new Abelian.Equation<string, int>()
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
        | _ -> failwith "Improperly structured row element head"



    // Free variable computations
    let rec typeKindsFree t =
        match t with
        | TVar (_, k) -> kindFree k
        | TDotVar (_, k) -> kindFree k
        | TCon (_, k) -> kindFree k
        | TSeq ts -> DotSeq.toList ts |> Seq.map typeKindsFree |> Set.unionMany
        | TApp (l, r) -> Set.union (typeKindsFree l) (typeKindsFree r)

        | TAnd (l, r) -> Set.union (typeKindsFree l) (typeKindsFree r)
        | TOr (l, r) -> Set.union (typeKindsFree l) (typeKindsFree r)
        | TNot n -> typeKindsFree n

        | TExponent (b, _) -> typeKindsFree b
        | TMultiply (l, r) -> Set.union (typeKindsFree l) (typeKindsFree r)

        | _ -> Set.empty

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

    let typeFree = typeFreeWithKinds >> Set.map fst

    let schemeFree s = Set.difference (typeFree s.Body) (Set.ofList (List.map fst s.QuantifiedTypes))


    // Kind computations
    exception MixedDataAndNestedSequences of DotSeq.DotSeq<Type>
    exception KindNotExpected of Kind * List<Kind>
    exception KindInvalidInContext of Kind

    let expectKindsExn pred expected test =
        if pred expected
        then 
            if List.forall (fun t -> kindEq t expected && pred t) test
            then expected
            else raise (KindNotExpected (expected, test))
        else raise (KindInvalidInContext expected)
    
    let gatherKind k kinds =
        List.fold (fun res k -> if kindEq res k then res else raise (KindNotExpected (k, kinds))) k kinds

    let expectKindPredExn pred test =
        if pred test
        then test
        else raise (KindInvalidInContext test)

    let rec typeKindExn t =
        match t with
        | TWildcard k -> k
        | TVar (_, k) -> k
        | TDotVar (_, k) -> k
        | TCon (_, k) -> k

        | TTrue k -> expectKindPredExn isKindBoolean k
        | TFalse k -> expectKindPredExn isKindBoolean k
        | TAnd (l, r) -> expectKindsExn isKindBoolean (typeKindExn l) [(typeKindExn r)]
        | TOr (l, r) -> expectKindsExn isKindBoolean (typeKindExn l) [(typeKindExn r)]
        | TNot n -> expectKindPredExn isKindBoolean (typeKindExn n)

        | TAbelianOne k -> expectKindPredExn isKindAbelian k
        | TExponent (b, _) -> expectKindPredExn isKindAbelian (typeKindExn b)
        | TMultiply (l, r) -> expectKindsExn isKindAbelian (typeKindExn l) [(typeKindExn r)]
        | TFixedConst _ -> primFixedKind

        | TRowExtend k -> karrow k (karrow (krow k) (krow k))
        | TEmptyRow k -> krow k

        | TSeq ts ->
            match ts with
            | ts when DotSeq.any isSeq ts && DotSeq.any isInd ts -> raise (MixedDataAndNestedSequences ts)
            | DotSeq.SInd (ht, tss) when DotSeq.all isInd tss ->
                kseq (gatherKind (typeKindExn ht) (DotSeq.toList tss |> List.map typeKindExn))
            | DotSeq.SEnd -> kseq KAny
            | ts -> DotSeq.map typeKindExn ts |> maxKindsExn |> kseq
        | TApp (l, r) -> applyKindExn (typeKindExn l) (typeKindExn r)
    
    let isTypeWellKinded ty =
        try
            let k = typeKindExn ty
            true
        with
            | ex -> false


    /// Perform many basic simplification steps to minimize the Boolean equations, fixed-size type expressions,
    /// and non-scoped labeled rows.
    let rec simplifyType ty =
        let k =
            try
                typeKindExn ty
            with
            | KindNotExpected (l, r) -> failwith $"Kind {l} <> {r} in {ty}"
        match ty with
        | TAnd _ -> typeToBooleanEqn ty |> Boolean.minimize |> booleanEqnToType k
        | TOr _ -> typeToBooleanEqn ty |> Boolean.minimize |> booleanEqnToType k
        | TNot _ -> typeToBooleanEqn ty |> Boolean.minimize |> booleanEqnToType k
        | _ when k = primFixedKind ->
            let eqn = typeToFixedEqn ty
            let simplified = Map.toSeq eqn.Constants |> Seq.sumBy (fun (b, e) -> b * e)
            fixedEqnToType (new Abelian.Equation<string, int>(eqn.Variables, if simplified = 0 then Map.empty else Map.empty.Add(simplified, 1)))
        | _ when k = primMeasureKind ->
            abelianEqnToType primMeasureKind (typeToUnitEqn ty)
        | TApp (l, r) -> typeApp (simplifyType l) (simplifyType r)
        | TSeq ts -> typeSeq (DotSeq.map simplifyType ts)
        | b -> b


    let rec prettyType ty =
        match ty with
        //| _ when typeKindExn ty = primMeasureKind -> (typeToUnitEqn ty).FractionString ()
        | TWildcard _ -> "_"
        | TVar (n, KRow _) -> $"{n}..."
        | TVar (n, k) -> $"{n}"
        | TDotVar (n, _) -> $"{n}..."
        | TCon (n, _) -> n
        | TTrue _ -> "True"
        | TFalse _ -> "False"
        | TAnd (l, r) -> $"({prettyType l} && {prettyType r})"
        | TOr (l, r) -> $"({prettyType l} || {prettyType r})"
        | TNot b -> $"!{prettyType b}"
        | TAbelianOne _ -> "one"
        | TExponent (b, p) -> $"{prettyType b}^{p}"
        | TMultiply (l, r) -> $"({prettyType l}*{prettyType r})"
        | TFixedConst n -> $"{n}"
        | TRowExtend _ -> "rowCons"
        | TEmptyRow _ -> "."
        | TSeq ts -> $"{DotSeq.rev ts |> DotSeq.map prettyType}"
        | TApp (TApp (TRowExtend _, e), TVar (v, _)) -> $"{v}..., {prettyType e}"
        | TApp (TApp (TRowExtend _, e), r) -> $"{prettyType r}, {prettyType e}"
        | TApp (TApp (TCon (PrimConstrainedCtorName, _), TApp (TCon (PrimConstraintTupleCtorName, _), TSeq DotSeq.SEnd)), fn) -> $"{prettyType fn}"
        | TApp (TApp (TCon (PrimConstrainedCtorName, _), TApp (TCon (PrimConstraintTupleCtorName, _), TSeq cnstrs)), fn) -> $"{DotSeq.map prettyType cnstrs} => {prettyType fn}"
        | TApp (TApp (TApp (TApp (TApp (TCon (PrimFunctionCtorName, _), e), p), t), i), o) ->
            $"{prettyType i} ===[ {prettyType e} ][ {prettyType p} ][ {prettyType t} ]==> {prettyType o}"
        | TApp (TApp (TCon (PrimTrackedCtorName, _), (TApp _ as d)), s) -> $"({prettyType d})^{prettyType s}"
        | TApp (TApp (TCon (PrimTrackedCtorName, _), d), s) -> $"{prettyType d}^{prettyType s}"
        | TApp (l, (TApp (TApp (TCon (PrimTrackedCtorName, _), _), _) as r)) -> $"{prettyType l} {prettyType r}"
        | TApp (l, (TApp _ as r)) -> $"{prettyType l} ({prettyType r})"
        | TApp (l, r) -> $"{prettyType l} {prettyType r}"