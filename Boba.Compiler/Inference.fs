namespace Boba.Compiler

module Inference =

    open Boba.Core
    open Boba.Core.Common
    open Boba.Core.Kinds
    open Boba.Core.Types
    open Boba.Core.TypeBuilder
    open Boba.Core.Unification
    open Boba.Core.Fresh
    open Boba.Core.Environment
    open Condenser

    let composeWordTypes leftType rightType =
        let resTy =
            qualType (List.append leftType.Context rightType.Context)
                (mkFunctionType
                    (functionTypeEffs leftType.Head)
                    (functionTypePerms leftType.Head)
                    (functionTypeTotal leftType.Head)
                    (functionTypeIns leftType.Head)
                    (functionTypeOuts rightType.Head)
                    (functionTypeSharing leftType.Head))
        let effConstr = { Left = functionTypeEffs leftType.Head; Right = functionTypeEffs rightType.Head }
        let permConstr = { Left = functionTypePerms leftType.Head; Right = functionTypePerms rightType.Head }
        let totConstr = { Left = functionTypeTotal leftType.Head; Right = functionTypeTotal rightType.Head }
        let insOutsConstr = { Left = functionTypeOuts leftType.Head; Right = functionTypeIns rightType.Head }
        // assumption: sharing is always false (shared) here
        (resTy, [effConstr; permConstr; totConstr; insOutsConstr])

    let freshTypeVar (fresh : FreshVars) prefix kind = typeVar (fresh.Fresh prefix) kind
    let freshValVar fresh = freshTypeVar fresh "z" KValue

    let freshExpressionAttributes (fresh : FreshVars) =
        let e = typeVar (fresh.Fresh "e") (KRow KEffect)
        let p = typeVar (fresh.Fresh "p") (KRow KPermission)
        let t = typeVar (fresh.Fresh "t") KTotality
        (e, p, t)

    // Generates a simple polymorphic expression type of the form (a... -> a...)
    let freshNoChange (fresh : FreshVars) =
        let io = TSeq (DotSeq.SDot (typeVar (fresh.Fresh "a") KValue, DotSeq.SEnd))
        let (e, p, t) = freshExpressionAttributes fresh
        qualType [] (mkFunctionType e p t io io (TFalse KSharing))

    // Generates a simple polymorphic expression type of the form (a... -> a... ty)
    let freshConst (fresh : FreshVars) ty =
        let rest = DotSeq.SDot (typeVar (fresh.Fresh "a") KValue, DotSeq.SEnd)
        let s = typeVar (fresh.Fresh "s") KSharing
        let i = TSeq rest
        let o = TSeq (DotSeq.SInd (mkValueType ty s, rest))
        let (e, p, t) = freshExpressionAttributes fresh
        qualType [] (mkFunctionType e p t i o (TFalse KSharing))

    let freshConstScheme fresh ty = { Quantified = [("a", KValue)]; Body = freshConst fresh ty }

    let freshVarScheme fresh = freshConstScheme fresh (freshValVar fresh)

    let freshConstWord (fresh : FreshVars) ty word = (freshConst fresh ty, [], [word])

    /// The sharing attribute on a closure is the disjunction of all of the free variables referenced
    /// by the closure, forcing it to be unique if any of the free variables it references are also unique.
    let sharedClosure env expr =
        List.ofSeq (Syntax.exprFree expr)
        |> List.map (Environment.lookup env >> Option.map (fun entry -> schemeSharing entry.Type))
        |> List.collect Option.toList
        |> attrsToDisjunction KSharing

    let rec inferPattern fresh pattern =
        match pattern with
        | Syntax.PTuple _ -> failwith "Inference for tuple patterns not yet implemented."
        | Syntax.PList _ -> failwith "Inference for list patterns not yet implemented."
        | Syntax.PVector _ -> failwith "Inference for vector patterns not yet implemented."
        | Syntax.PSlice _ -> failwith "Inference for slice patterns not yet implemented."
        | Syntax.PRecord _ -> failwith "Inference for record patterns not yet implemented."
        | Syntax.PConstructor _ -> failwith "Inference for data constructor patterns not yet implemented."
        | Syntax.PNamed (n, p) ->
            let (vs, ty) = inferPattern fresh p
            (n, ty) :: vs, ty
        | Syntax.PRef (r) ->
            let (vs, ty) = inferPattern fresh r
            (vs, )

    let rec inferExpr (fresh : FreshVars) env expr =
        let exprInferred = List.map (inferWord fresh env) expr
        let composed =
            List.fold
                (fun (ty, constrs, expanded) (next, newConstrs, nextExpand) ->
                    let (uniTy, uniConstrs) = composeWordTypes ty next
                    (uniTy, append3 constrs newConstrs uniConstrs, List.append expanded nextExpand))
                (freshNoChange fresh, [], [])
                exprInferred
        composed
    and inferWord fresh env word =
        match word with
        | Syntax.EStatementBlock ss ->
            let (ssTy, ssCnstrs, ssPlc) = inferBlock fresh env ss
            (ssTy, ssCnstrs, [Syntax.EStatementBlock ssPlc])
        | Syntax.EDecimal d ->
            freshConstWord fresh (typeApp (TPrim (PrFloat d.Size)) (typeVar (fresh.Fresh "u") KUnit)) word
        | Syntax.EInteger i ->
            freshConstWord fresh (typeApp (TPrim (PrInteger i.Size)) (typeVar (fresh.Fresh "u") KUnit)) word
        | Syntax.EString _ ->
            freshConstWord fresh (typeCon "String" KData) word
        | Syntax.EDo ->
            let irest = DotSeq.SDot (typeVar (fresh.Fresh "a") KValue, DotSeq.SEnd)
            let i = TSeq irest
            let o = TSeq (DotSeq.SDot (typeVar (fresh.Fresh "b") KValue, DotSeq.SEnd))
            let s = typeVar (fresh.Fresh "s") KSharing
            let (e, p, t) = freshExpressionAttributes fresh
            let called = mkFunctionType e p t i o s
            let caller = mkFunctionType e p t (TSeq (DotSeq.SInd (called, irest))) o (TFalse KSharing)
            (qualType [] caller, [], [Syntax.EDo])
    and inferBlock fresh env stmts =
        match stmts with
        | Syntax.SLet { Matcher = ps; Body = b } :: ss ->
            match Syntax.getFlatVars ps with
            | Some vars ->
                let (bTy, bCnstr, bPlc) = inferExpr fresh env b
                let varEnv = List.fold (fun env v -> extendVar env v (freshVarScheme fresh)) env vars
                let (ssTy, ssCnstr, ssPlc) = inferBlock fresh varEnv ss

                [WVars (vars, genCoreExpr matchEnv clause.Body)]
            | None -> failwith "Patterns more complex than simple variables not yet allowed."
        | Syntax.SLocals :: ss -> failwith "Local functions not yet implemented."
        | Syntax.SExpression e :: ss ->
            let (eTy, eCnstr, ePlc) = inferExpr fresh env e
            let (sTy, sCnstr, sPlc) = inferBlock fresh env ss
            let (uniTy, uniConstrs) = composeWordTypes eTy sTy
            (uniTy, append3 eCnstr sCnstr uniConstrs, Syntax.SExpression ePlc :: sPlc)
