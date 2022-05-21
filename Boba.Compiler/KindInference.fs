namespace Boba.Compiler

module KindInference =

    open System
    open Boba.Core
    open Boba.Core.Common
    open Boba.Core.Kinds
    open Boba.Core.Types
    open Boba.Core.Unification
    open Boba.Core.Fresh
    open Boba.Core.Environment

    let lookupTypeOrFail env name ctor =
        match lookupType env name with
        | Some k -> k, [], ctor name k
        | None -> failwith $"Could not find '{name}' in type environment during kind inference."

    let freshKind (fresh : FreshVars) = KVar (fresh.Fresh "k")

    let freshCtor fresh ctor =
        let k = freshKind fresh
        k, [], ctor k

    let rec kindInfer fresh env sty =
        match sty with
        | Syntax.STVar n -> lookupTypeOrFail env n.Name typeVar
        | Syntax.STDotVar n -> lookupTypeOrFail env n.Name typeDotVar
        | Syntax.STCon n -> lookupTypeOrFail env n.Name.Name typeCon
        | Syntax.STPrim p -> primKind p, [], TPrim p
        | Syntax.STTrue -> freshCtor fresh TTrue
        | Syntax.STFalse -> freshCtor fresh TFalse
        | Syntax.STAnd (l, r) -> simpleBinaryCon fresh env l r TAnd
        | Syntax.STOr (l, r) -> simpleBinaryCon fresh env l r TOr
        | Syntax.STNot n -> simpleUnaryCon fresh env n TNot
        | Syntax.STAbelianOne -> freshCtor fresh TAbelianOne
        | Syntax.STExponent (b, p) -> simpleUnaryCon fresh env b (fun t -> TExponent (t, Int32.Parse p.Value))
        | Syntax.STMultiply (l, r) -> simpleBinaryCon fresh env l r TMultiply
        | Syntax.STFixedConst c -> KFixed, [], TFixedConst (Int32.Parse c.Value)
        | Syntax.STRowExtend ->
            let k = freshKind fresh
            karrow k (karrow (KRow k) (KRow k)), [], TRowExtend k
        | Syntax.STRowEmpty ->
            let k = freshKind fresh
            KRow k, [], TEmptyRow k
        | Syntax.STSeq (ts, k) ->
            if DotSeq.length ts = 0
            then
                let seqKind = freshKind fresh
                KSeq seqKind, [{ LeftKind = seqKind; RightKind = k }], typeSeq DotSeq.SEnd k
            else
                let ks = DotSeq.map (kindInfer fresh env) ts
                let seqKind =
                    DotSeq.at 0 ks
                    |> Option.defaultWith (fun () -> failwith "No element in type sequence")
                    |> (fun (k, _, _) -> k)
                let cstrs = DotSeq.map (fun (_, cs, _) -> cs) ks |> DotSeq.fold List.append []
                let allSeqKindsEq = DotSeq.map (fun (k, _, _) -> { LeftKind = seqKind; RightKind = k }) ks |> DotSeq.toList
                let allCstrs = append3 [{ LeftKind = seqKind; RightKind = k }] allSeqKindsEq cstrs
                KSeq seqKind, allCstrs, TSeq (DotSeq.map (fun (_, _, t) -> t) ks, k)
        | Syntax.STApp (l, r) ->
            let (lk, lcstrs, lt) = kindInfer fresh env l
            let (rk, rcstrs, rt) = kindInfer fresh env r
            let ret = freshKind fresh
            ret, append3 [{ LeftKind = lk; RightKind = karrow rk ret }] lcstrs rcstrs, typeApp lt rt
    and simpleBinaryCon fresh env l r ctor =
        let (lk, lcstrs, lt) = kindInfer fresh env l
        let (rk, rcstrs, rt) = kindInfer fresh env r
        lk, append3 [{ LeftKind = lk; RightKind = rk }] lcstrs rcstrs, ctor (lt, rt)
    and simpleUnaryCon fresh env b ctor =
        let (k, cstrs, t) = kindInfer fresh env b
        k, cstrs, ctor t

    let kindAnnotateType fresh env (ty : Syntax.SType) =
        let kenv = Syntax.stypeFree ty |> Set.fold (fun e v -> addTypeCtor e v (freshKind fresh)) env
        let (inf, constraints, ty) = kindInfer fresh kenv ty
        let subst = solveKindConstraints constraints
        try
            let ann = typeKindSubstExn subst ty
            assert (isTypeWellKinded ann)
            ann
        with
            | KindUnifyMismatchException (l, r) -> failwith $"{l} ~ {r} failed to unify."
    
    let inferConstructorKinds fresh env (ctor: Syntax.Constructor) =
        let ctorVars = List.map Syntax.stypeFree (ctor.Result :: ctor.Components) |> Set.unionMany
        let kEnv = Set.fold (fun env v -> addTypeCtor env v (freshKind fresh)) env ctorVars
        let (kinds, constrs, tys) = List.map (kindInfer fresh kEnv) ctor.Components |> List.unzip3
        let ctorKind, ctorConstrs, ctorTy = kindInfer fresh kEnv ctor.Result
        // every component in a constructor should be of kind Value
        let valConstrs = List.map (fun k -> { LeftKind = k; RightKind = KValue }) kinds
        // the result component must also be of kind data
        let dataConstr = { LeftKind = ctorKind; RightKind = KData }
        List.append kinds [ctorKind], dataConstr :: append3 ctorConstrs valConstrs (List.concat constrs), List.append tys [ctorTy]