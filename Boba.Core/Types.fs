namespace Boba.Core

module Types =

    open System.Diagnostics
    open Common
    open Kinds

    /// It is convenient throughout the implementation of the type system to be able to pattern match on some primitive type
    /// constructors. Using the standard type constructor, and making the primitives constants, would result in pattern matching
    /// on the string name of the primitive, which is bug prone and far less maintainable. However, we don't want to clutter the
    /// Type data structure with noisy type constants, so the primitives have been separated out here.
    type Prim =
        // Misc
        | PValue
        | PFunction
        | PRef

        // Collection
        | PTuple
        | PList
        | PVector
        | PSlice

        // Structural
        | PRecord
        | PVariant

    let primKind prim =
        match prim with
        | PValue -> karrow KData (karrow KSharing KValue)
        | PFunction -> karrow KEffects (karrow (kseq KValue) (karrow (kseq (KValue)) KData))
        | PRef -> karrow KHeap (karrow KValue KData)

        | PTuple -> karrow (kseq KValue) KData
        | PList -> karrow KValue KData
        | PVector -> karrow KFixed (karrow KValue KData)
        | PSlice -> karrow KFixed (karrow KValue KData)

        | PRecord -> karrow KFields KData
        | PVariant -> karrow KFields KData

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
    type Type =
        /// A type variable stands in for a particular type, or a sequence of types. The indexes component allows this variable to
        /// select down n levels in a 'sequence substitution', where n is the length of the indexes list. This feature eliminates the
        /// need for generating fresh variables during substitution, which would otherwise greatly complicate sequence substitution
        /// during type inference.
        | TVar of name: string * kind: Kind
        /// Represents a rigid type constructor with an explicit kind. Equality of type constructors is based on both name and kind.
        | TCon of name: string * kind: Kind
        | TPrim of prim: Prim

        | TTrue of kind: Kind
        | TFalse of kind: Kind
        | TAnd of left: Type * right: Type
        | TOr of left: Type * right: Type
        | TNot of body: Type

        | TAbelianOne of kind: Kind // identity type for any kind of abelian equation
        | TExponent of body: Type * power: int
        | TMultiply of left: Type * right: Type
        | TFixedConst of num: int // for the numeric constants of fixed size types

        | TRowExtend of kind: Kind
        | TEmptyRow of kind: Kind

        | TSeq of seq: DotSeq.DotSeq<Type>
        | TApp of cons: Type * arg: Type

    type Predicate = { Name: string; Argument: Type }

    type QualifiedType = { Context: List<Predicate>; Head: Type }

    type TypeScheme = { Quantified: List<(string * Kind)>; Body: QualifiedType }


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

    let rec flattenSeqs t =
        match t with
        | TSeq ts -> DotSeq.toList ts |> List.map flattenSeqs |> List.concat
        | _ -> [t]


    // Functional constructors
    let typeVar name kind = TVar (name, kind)
    let typeCon name kind = TCon (name, kind)
    let typeApp cons arg = TApp (cons, arg)
    let typeUnit eqn inds = TUnit (eqn, inds)
    let typeFixed eqn inds = TFixed (eqn, inds)
    let typeField field param row = typeApp (typeApp (typeApp (TPrim PFieldExtend) (TPrim (PField field))) param) row

    let typeNot n = typeApp (TPrim PSharingNot) n
    let typeOr l r = typeApp (typeApp (TPrim PSharingOr) l) r
    let typeAnd l r = typeApp (typeApp (TPrim PSharingAnd) l) r
 
    let predType name arg = { Name = name; Argument = arg }

    let qualType context head = { Context = context; Head = head }

    let schemeType quantified body = { Quantified = quantified; Body = body }

    let rec toBooleanEqn ty =
        match ty with
        | TTrue _ -> Boolean.BTrue
        | TFalse _ -> Boolean.BFalse
        | TVar (n, k) when isKindBoolean k -> Boolean.BVar n
        | TAnd (l, r) -> Boolean.BAnd (toBooleanEqn l, toBooleanEqn r)
        | TOr (l, r) -> Boolean.BOr (toBooleanEqn l, toBooleanEqn r)
        | TNot n -> Boolean.BNot (toBooleanEqn n)
        | _ -> failwith "Tried to convert a non-Boolean type to a Boolean equation"

    let rec booleanEqnToType kind eqn =
        match eqn with
        | Boolean.BTrue -> TTrue kind
        | Boolean.BFalse -> TFalse kind
        | Boolean.BVar n -> TVar (n, kind)
        | Boolean.BAnd (l, r) -> TAnd (booleanEqnToType kind l, booleanEqnToType kind r)
        | Boolean.BOr (l, r) -> TOr (booleanEqnToType kind l, booleanEqnToType kind r)
        | Boolean.BNot n -> TNot (booleanEqnToType kind n)
    
    let attrsToDisjunction attrs kind =
        List.map toBooleanEqn attrs
        |> List.fold (fun eqn tm -> Boolean.BOr (eqn, tm)) Boolean.BFalse
        |> Boolean.simplify
        |> booleanEqnToType kind


    // Free variable computations
    let rec typeFree t =
        match t with
        | TVar (n, _) -> Set.singleton n
        | TSeq ts -> DotSeq.toList ts |> List.map typeFree |> Set.unionMany
        | TApp (l, r) -> Set.union (typeFree l) (typeFree r)

        | TAnd (l, r) -> Set.union (typeFree l) (typeFree r)
        | TOr (l, r) -> Set.union (typeFree l) (typeFree r)
        | TNot n -> typeFree n

        | TExponent (b, _) -> typeFree b
        | TMultiply (l, r) -> Set.union (typeFree l) (typeFree r)

        | _ -> Set.empty

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
        | TCon (_, k) -> k
        | TPrim p -> primKind p

        | TTrue k -> k
        | TFalse k -> k
        | TAnd (l, r) -> expectKindsExn isKindBoolean (typeKindExn l) [(typeKindExn r)]
        | TOr (l, r) -> expectKindsExn isKindBoolean (typeKindExn l) [(typeKindExn r)]
        | TNot n -> expectKindPredExn isKindBoolean (typeKindExn n)

        | TAbelianOne k -> k
        | TExponent (b, _) -> expectKindPredExn isKindAbelian (typeKindExn b)
        | TMultiply (l, r) -> expectKindsExn isKindAbelian (typeKindExn l) [(typeKindExn r)]
        | TFixedConst _ -> KFixed

        | TRowExtend k -> k
        | TEmptyRow k -> k

        | TSeq ts ->
            match ts with
            | ts when DotSeq.all isInd ts -> KData
            | ts when DotSeq.any isSeq ts && DotSeq.any isInd ts -> raise (MixedDataAndNestedSequences ts)
            | ts -> DotSeq.map typeKindExn ts |> maxKindsExn
        | TApp (l, r) -> applyKindExn (typeKindExn l) (typeKindExn r)

    let predKindExn p = typeKindExn p.Argument


    /// Perform many basic simplification steps to minimize a the Boolean equations in a type as much as possible.
    let rec simplifyType ty =
        let k = typeKindExn ty
        if isKindBoolean k
        then toBooleanEqn ty |> Boolean.simplify |> booleanEqnToType k
        else
            match ty with
            | TApp (l, r) -> typeApp (simplifyType l) (simplifyType r)
            | TSeq ts -> DotSeq.map simplifyType ts |> TSeq
            | b -> b


    // Substitution computations
    let rec getsub (inds : int list) (sub : Type) =
        match (inds, sub) with
        | ([], s) -> s
        | ([i], TSeq s) -> 
            match DotSeq.at i s with
            | Option.Some t -> t
            | Option.None -> failwith "Tried to index outside the bounds of the sequence"
        | (i :: is, TSeq s) ->
            match DotSeq.at i s with
            | Option.Some t -> getsub is t
            | Option.None -> failwith "Tried to index outside the bounds of the sequence"
        | _ -> failwith "Tried to index a non-sequence type."

    let zipExtendRest (ts : Type) =
        match ts with
        | TSeq (DotSeq.SInd (_, rs)) -> TSeq rs
        | TSeq (DotSeq.SDot (_, rs)) -> TSeq rs
        | TSeq (DotSeq.SEnd) -> failwith "Tried to zipExtendRest an empty sequence."
        | any -> any

    let rec copyAt (i : int) (t : Type) =
        match t with
        | TVar (n, k, inds) -> typeVar n k (List.append inds [i])
        | TCon _ -> t
        | TPrim _ -> t
        | TUnit (eqn, inds) -> TUnit (eqn, List.append inds [i])
        | TFixed (eqn, inds) -> TFixed (eqn, List.append inds [i])
        | TApp (l, r) -> TApp (copyAt i l, copyAt i r)
        | TSeq ts -> DotSeq.map (copyAt i) ts |> TSeq

    let zipExtendHeads (i : int) (ts : Type) =
        match ts with
        | TSeq (DotSeq.SInd (b, _)) -> b
        | TSeq (DotSeq.SDot (b, _)) -> b
        | TSeq (DotSeq.SEnd) -> failwith "Tried to zipExtendHeads an empty sequence."
        | any -> copyAt i any

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
        let rec zipExtendInc ts i =
            if DotSeq.any isSeq ts
            then if DotSeq.all (fun t -> emptySeqOrInd t) ts
                 then DotSeq.SEnd
                 else if DotSeq.any (fun t -> isSeq t && emptySeqOrInd t) ts
                 then failwith "zipExtend sequences were of different length."
                 else (dotOrInd ts) (TSeq (zipExtend (DotSeq.map (zipExtendHeads i) ts)), zipExtendInc (DotSeq.map zipExtendRest ts) (1 + i))
            else ts

        if DotSeq.all isSeq ts && DotSeq.anyIndInSeq ts
        then DotSeq.map (fun t -> getSeq t |> zipExtend |> TSeq) ts
        else zipExtendInc (spliceDots ts) 0

    let extend (t: Type) (len: int) = [ for i in 0..len-1 do yield copyAt i t ] |> DotSeq.ofList

    let rec seqToDisjunctions seq =
        match seq with
        | DotSeq.SEnd -> TPrim PShared
        | DotSeq.SInd (e, DotSeq.SEnd) -> e
        | DotSeq.SDot (e, DotSeq.SEnd) -> e
        | DotSeq.SInd (e, ds) -> typeApp (typeApp (TPrim PSharingOr) e) (seqToDisjunctions ds)
        | DotSeq.SDot (e, ds) -> typeApp (typeApp (TPrim PSharingOr) e) (seqToDisjunctions ds)

    let rec fixApp (t : Type) =
        match t with
        | TApp (TSeq ls, TSeq rs) -> DotSeq.zipWith ls rs typeApp |> DotSeq.map fixApp |> TSeq
        | TApp (TSeq ls, r) -> DotSeq.zipWith ls (extend r (DotSeq.length ls)) typeApp |> DotSeq.map fixApp |> TSeq
        // special cases for dots inside boolean equations, which get transformed into nested disjunctions when substituted with a sequence
        | TApp (TPrim PSharingDot, TSeq rs) when typeKindExn (TSeq rs) = kseq KSharing -> seqToDisjunctions rs
        | TApp (TPrim PSharingDot, TSeq rs) -> DotSeq.zipWith (extend (TPrim PSharingDot) (DotSeq.length rs)) rs typeApp |> DotSeq.map fixApp |> TSeq
        | TApp (l, TSeq rs) ->
            // special case for type constructors that take sequences as arguments: don't bubble the sequence up!
            let canApplySeq =
                match typeKindExn l with
                | KArrow (arg, _) -> arg = typeKindExn (TSeq rs)
                | _ -> false
            if canApplySeq
            then typeApp l (TSeq rs)
            else DotSeq.zipWith (extend l (DotSeq.length rs)) rs typeApp |> DotSeq.map fixApp |> TSeq
        | TApp _ -> t
        | _ -> invalidArg (nameof t) "Called fixApp on non TApp type"

    let rec unitSubst (rep: Abelian.Equation<string, string>) target sub inds =
        match sub with
        | TSeq ts -> DotSeq.mapi (fun subt ind -> unitSubst rep target subt (ind :: inds)) ts |> TSeq
        | TUnit (eqnsub, []) -> TUnit (rep.Substitute target eqnsub, inds)
        | TVar (n, KUnit, []) -> TUnit (rep.Substitute target (new Abelian.Equation<string, string>(n)), inds)
        | _ -> invalidArg (nameof sub) $"Cannot substitute {sub} into Boolean equation {rep}"

    let rec fixedSubst (rep: Abelian.Equation<string, int>) target sub inds =
        match sub with
        | TSeq ts -> DotSeq.mapi (fun subt ind -> fixedSubst rep target subt (ind :: inds)) ts |> TSeq
        | TFixed (eqnsub, []) -> TFixed (rep.Substitute target eqnsub, inds)
        | TVar (n, KFixed, []) -> TFixed (rep.Substitute target (new Abelian.Equation<string, int>(n)), inds)
        | _ -> invalidArg (nameof sub) $"Cannot substitute {sub} into Boolean equation {rep}"

    let rec typeSubstExn (target: string) (sub: Type) (rep : Type) =
        match rep with
        | TCon (_, _) -> rep
        | TPrim _ -> rep
        | TVar (n, _, inds) -> if n = target then getsub inds sub else rep
        | TUnit (eqn, inds) ->
            if eqn.Free().Contains target
            then getsub inds sub |> (fun subsub -> unitSubst eqn target subsub [])
            else rep
        | TFixed (eqn, inds) ->
            if eqn.Free().Contains target
            then getsub inds sub |> (fun subsub -> fixedSubst eqn target subsub [])
            else rep
        | TApp (l,r) -> TApp (typeSubstExn target sub l, typeSubstExn target sub r) |> fixApp
        | TSeq (ts) -> DotSeq.map (typeSubstExn target sub) ts |> zipExtend |> TSeq

    let applySubstTypeExn subst target = Map.fold (fun ty var sub -> typeSubstExn var sub ty) target subst
    
    let composeSubstExn subl subr = Map.map (fun _ v -> applySubstTypeExn subl v) subr |> mapUnion fst subl

    let predSubstExn var sub pred = { Name = pred.Name; Argument = typeSubstExn var sub pred.Argument }
    
    let qualSubstExn var sub qual = { Context = List.map (predSubstExn var sub) qual.Context; Head = typeSubstExn var sub qual.Head }
    
    let applySubstPredExn subst pred = Map.fold (fun pr var sub -> predSubstExn var sub pr) pred subst
    
    let applySubstContextExn subst context = List.map (applySubstPredExn subst) context


    // Head noraml form computations
    let rec typeHeadNormalForm t =
        match t with
        | TVar _ -> true
        | TCon _ -> false
        | TPrim _ -> false
        | TSeq _ -> false
        | TApp (l, _) -> typeHeadNormalForm l

    let predHeadNoramlForm p = typeHeadNormalForm p.Argument


    // One-way matching of types
    let mergeSubstExn (s1 : Map<string, Type>) (s2 : Map<string, Type>) =
        let agree = Set.forall (fun v -> s1.[v] = s2.[v]) (Set.intersect (mapKeys s1) (mapKeys s2))
        if agree then mapUnion fst s1 s2 else invalidOp "Substitutions could not be merged"

    let rec typeMatchExn l r =
        match (l, r) with
        | (TVar (n, k))
        | (TVar (n, k, _), r) -> if k = typeKindExn r then Option.Some (Map.add n r Map.empty) else Option.None
        | (TCon _, TCon _) -> if l = r then Option.Some Map.empty else Option.None
        | (TApp (ll, lr), TApp (rl, rr)) ->
            maybe
                {
                let! lm = typeMatchExn ll rl
                let! rm = typeMatchExn lr rr
                let merged = mergeSubstExn lm rm
                return merged
                }
        | _ -> Option.None

    let isTypeMatch l r =
        match typeMatchExn l r with
        | Some _ -> true
        | None -> false


    //// Unification of types
    //let rec typeUnifyExn l r =
    //    match (l, r) with
    //    | (_, _) when l = r -> Option.Some (Map.empty)
    //    | (TVar (nl, kl), r) when kl = typeKindExn r && not (Set.contains nl (typeFree r)) -> Option.Some (Map.add nl r Map.empty)
    //    | (l, TVar (nr, kr)) when kr = typeKindExn l && not (Set.contains nr (typeFree l)) -> Option.Some (Map.add nr l Map.empty)
    //    | (TApp (ll, lr), TApp (rl, rr)) ->
    //        maybe
    //            {
    //            let! lu = typeUnifyExn ll rl
    //            let! ru = typeUnifyExn (applySubstTypeExn lu lr) (applySubstTypeExn lu rr)
    //            return composeSubstExn ru lu
    //            }
    //    | _ -> Option.None

    //let typeOverlap l r =
    //    match typeUnifyExn l r with
    //    | Some _ -> true
    //    | None -> false