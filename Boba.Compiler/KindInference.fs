namespace Boba.Compiler

module KindInference =

    open System
    open Boba.Core
    open Boba.Core.Common
    open Boba.Core.Kinds
    open Boba.Core.Types
    open Boba.Core.Substitution
    open Boba.Core.Unification
    open Boba.Core.Fresh
    open Boba.Core.Environment

    let lookupTypeOrFail fresh env name ctor =
        match lookupType env name with
        | Some ksch -> 
            let instK = instantiateKinds fresh ksch
            instK, [], ctor name instK
        | None -> failwith $"Could not find '{name}' in type environment during kind inference."

    /// Create a fresh kind variable.
    let freshKind (fresh : FreshVars) = KVar (fresh.Fresh "k")

    /// Using the given type constructor parameterized by a kind, return the fresh
    /// kind variable `k`, a list of generated kind constraints, and the constructor
    /// assigned kind `k`.
    let freshCtor fresh ctor =
        let k = freshKind fresh
        k, [], ctor k

    /// Under the given type environment, transform the unkinded input type into
    /// a well-kinded type if possible. Returns the resulting kind of the newly
    /// annotated type, a list of kind constraints that can be solved to determine
    /// the most-general kind, and the annotated type.
    let rec kindInfer fresh env sty =
        match sty with
        | Syntax.STWildcard ->
            let k = freshKind fresh
            k, [], TWildcard k
        | Syntax.STVar n -> lookupTypeOrFail fresh env n.Name typeVar
        | Syntax.STDotVar n -> lookupTypeOrFail fresh env n.Name typeDotVar
        | Syntax.STCon n -> lookupTypeOrFail fresh env n.Name.Name typeCon
        | Syntax.STTrue -> freshCtor fresh TTrue
        | Syntax.STFalse -> freshCtor fresh TFalse
        | Syntax.STAnd (l, r) -> simpleBinaryCon fresh env l r TAnd
        | Syntax.STOr (l, r) -> simpleBinaryCon fresh env l r TOr
        | Syntax.STNot n -> simpleUnaryCon fresh env n TNot
        | Syntax.STAbelianOne -> freshCtor fresh TAbelianOne
        | Syntax.STExponent (b, p) -> simpleUnaryCon fresh env b (fun t -> TExponent (t, Int32.Parse p.Value))
        | Syntax.STMultiply (l, r) -> simpleBinaryCon fresh env l r TMultiply
        | Syntax.STFixedConst c -> primFixedKind, [], TFixedConst (Int32.Parse c.Value)
        | Syntax.STRowExtend ->
            let k = freshKind fresh
            karrow k (karrow (KRow k) (KRow k)), [], TRowExtend k
        | Syntax.STRowEmpty ->
            let k = freshKind fresh
            KRow k, [], TEmptyRow k
        | Syntax.STSeq ts ->
            if DotSeq.length ts = 0
            then
                let seqKind = freshKind fresh
                KSeq seqKind, [], typeSeq DotSeq.SEnd
            else
                let ks = DotSeq.map (kindInfer fresh env) ts
                let seqKind =
                    DotSeq.at 0 ks
                    |> Option.defaultWith (fun () -> failwith "No element in type sequence")
                    |> (fun (k, _, _) -> k)
                let cstrs = DotSeq.map (fun (_, cs, _) -> cs) ks |> DotSeq.fold List.append []
                let allSeqKindsEq = DotSeq.map (fun (k, _, _) -> kindEqConstraint seqKind k) ks |> DotSeq.toList
                let allCstrs = List.append allSeqKindsEq cstrs
                KSeq seqKind, allCstrs, typeSeq (DotSeq.map (fun (_, _, t) -> t) ks)
        | Syntax.STApp (l, r) ->
            let lk, lcstrs, lt = kindInfer fresh env l
            let rk, rcstrs, rt = kindInfer fresh env r
            let ret = freshKind fresh
            ret, append3 [kindEqConstraint lk (karrow rk ret)] lcstrs rcstrs, typeApp lt rt
    and simpleBinaryCon fresh env l r ctor =
        let (lk, lcstrs, lt) = kindInfer fresh env l
        let (rk, rcstrs, rt) = kindInfer fresh env r
        lk, append3 [kindEqConstraint lk rk] lcstrs rcstrs, ctor (lt, rt)
    and simpleUnaryCon fresh env b ctor =
        let (k, cstrs, t) = kindInfer fresh env b
        k, cstrs, ctor t

    // Given an unannotated type, converts it into a type with kind annotations on constructors and variables,
    // and places the type variables in the type environment in an extend copy of the original environment.
    // Returns the annotated type and the extended environment copy. 
    let kindAnnotateTypeWithConstraints fresh expectedKind env (ty : Syntax.SType) =
        let free = Syntax.stypeFree ty |> Set.filter (fun v -> not (Map.containsKey v env.TypeConstructors))
        let kenv = free |> Set.fold (fun e v -> addTypeCtor e v (kindScheme [] (freshKind fresh))) env
        let (inf, constraints, ty) = kindInfer fresh kenv ty
        let subst = solveComposeAll fresh ((kindEqConstraint expectedKind inf) :: constraints)
        try
            let ann = typeSubstExn fresh subst ty
            if not (isTypeWellKinded ann)
            then
                printfn $"Non-well kinded annotated type : {ann}"
                assert (isTypeWellKinded ann)
            ann, free |> Set.fold (fun e v -> addTypeCtor e v (generalizeKind (kindSubst subst (lookupType kenv v |> Option.defaultWith (fun _ -> failwith "Should exist") |> instantiateKinds fresh)))) env
        with
            | UnifyKindMismatchException (l, r) -> failwith $"{l} ~ {r} failed to unify."

    // Given an unannotated type, converts it into a type with kind annotations on constructors and variables,
    // and places the type variables in the type environment in an extend copy of the original environment.
    // Returns the annotated type and the extended environment copy. 
    let kindAnnotateTypeWith fresh env (ty : Syntax.SType) =
        let free = Syntax.stypeFree ty |> Set.filter (fun v -> not (Map.containsKey v env.TypeConstructors))
        let kenv = free |> Set.fold (fun e v -> addTypeCtor e v (kindScheme [] (freshKind fresh))) env
        let (inf, constraints, ty) = kindInfer fresh kenv ty
        try
            let subst = solveComposeAll fresh constraints
            let ann = typeSubstExn fresh subst ty
            assert (isTypeWellKinded ann)
            ann, free |> Set.fold (fun e v -> addTypeCtor e v (generalizeKind (kindSubst subst (lookupType kenv v |> Option.defaultWith (fun _ -> failwith "Should exist") |> instantiateKinds fresh)))) env
        with
            | UnifyKindMismatchException (l, r) -> failwith $"{l} ~ {r} failed to unify."

    let kindAnnotateType fresh env (ty : Syntax.SType) =
        kindAnnotateTypeWith fresh env ty |> fst
    
    let kindAnnotateConstraint fresh env (cnstr : Syntax.SConstraint) =
        match cnstr with
        | Syntax.SCPredicate ty -> CHR.CPredicate (kindAnnotateType fresh env ty)
        | Syntax.SCEquality (l, r) -> CHR.CEquality (typeEqConstraint (kindAnnotateType fresh env l) (kindAnnotateType fresh env r))
    
    let inferConstructorKinds fresh env (ctor: Syntax.Constructor) =
        let ctorTypeFree = List.map Syntax.stypeFree (ctor.Result :: ctor.Components) |> Set.unionMany
        let kEnv = Set.fold (fun env v -> addTypeCtor env v (kindScheme [] (freshKind fresh))) env ctorTypeFree
        let (kinds, constrs, tys) = List.map (kindInfer fresh kEnv) ctor.Components |> List.unzip3
        let ctorKind, ctorConstrs, ctorTy = kindInfer fresh kEnv ctor.Result
        // every component in a constructor should be of kind Value
        let valConstrs = List.map (fun k -> kindEqConstraint k primValueKind) kinds
        // the result component must also be of kind data
        let dataConstr = kindEqConstraint ctorKind primDataKind
        ctorKind, dataConstr :: append3 ctorConstrs valConstrs (List.concat constrs), List.append tys [ctorTy]