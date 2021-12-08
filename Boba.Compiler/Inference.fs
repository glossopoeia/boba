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
    open Boba.Core.Predicates
    open Renamer

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
        let s = freshShareVar fresh
        let i = TSeq rest
        let o = TSeq (DotSeq.SInd (ty, rest))
        let (e, p, t) = freshExpressionAttributes fresh
        qualType [] (mkFunctionType e p t i o (TFalse KSharing))
    
    let freshPopped (fresh: FreshVars) tys =
        let rest = DotSeq.SDot (typeVar (fresh.Fresh "a") KValue, DotSeq.SEnd)
        let o = TSeq rest
        let i = TSeq (DotSeq.append (DotSeq.ofList (List.rev tys)) rest)
        let (e, p, t) = freshExpressionAttributes fresh
        qualType [] (mkFunctionType e p t i o (TFalse KSharing))

    let freshConstScheme fresh ty = { Quantified = [("a", KValue)]; Body = freshConst fresh ty }

    let freshVarScheme fresh = freshConstScheme fresh (freshValVar fresh)

    let freshConstWord (fresh : FreshVars) ty word = (freshConst fresh ty, [], [word])

    /// The sharing attribute on a closure is the disjunction of all of the free variables referenced
    /// by the closure, forcing it to be unique if any of the free variables it references are also unique.
    let sharedClosure env expr =
        List.ofSeq (Syntax.exprFree expr)
        |> List.map (lookup env >> Option.map (fun entry -> schemeSharing entry.Type))
        |> List.collect Option.toList
        |> attrsToDisjunction KSharing

    /// Here, when we instantiate a type from the type environment, we also do inline dictionary
    /// passing, putting in placeholders for the dictionaries that will get resolved to either a
    /// dictionary parameter or dictionary value during generalization.
    /// More details on this implementation tactic: "Implementing Type Classes", https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.53.3952&rep=rep1&type=pdf
    let instantiateAndAddPlaceholders fresh env name word =
        match lookup env name with
        | Some entry ->
            let instantiated = instantiateExn fresh entry.Type
            let replaced = 
                if entry.IsClassMethod
                then 
                    [Syntax.EMethodPlaceholder (name, instantiated.Context.Head)]
                elif entry.IsRecursive
                then [Syntax.ERecursivePlaceholder { Name = name; Argument = instantiated.Head }]
                else List.append (List.map Syntax.EOverloadPlaceholder instantiated.Context) [word]
            (instantiated, [], replaced)
        | None -> failwith $"Could not find {name} in the environment"

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
            (Syntax.nameToString n, ty) :: vs, ty
        | Syntax.PRef (r) ->
            let (vs, ty) = inferPattern fresh r
            (vs, freshRefType fresh ty)
        | Syntax.PWildcard -> ([], freshValVarShare fresh)
        | Syntax.PInteger i -> ([], mkValueType (freshIntType fresh i.Size) (freshShareVar fresh))
        | Syntax.PDecimal d -> ([], mkValueType (freshFloatType fresh d.Size) (freshShareVar fresh))
        | Syntax.PString _ -> ([], mkValueType (typeCon "String" KData) (freshShareVar fresh))
        | Syntax.PTrue _ -> ([], freshShareBoolType fresh)
        | Syntax.PFalse _ -> ([], freshShareBoolType fresh)

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
        | Syntax.EIdentifier id ->
            instantiateAndAddPlaceholders fresh env id.Name.Name word
        | Syntax.EDo ->
            let irest = DotSeq.SDot (typeVar (fresh.Fresh "a") KValue, DotSeq.SEnd)
            let i = TSeq irest
            let o = TSeq (DotSeq.SDot (typeVar (fresh.Fresh "b") KValue, DotSeq.SEnd))
            let s = typeVar (fresh.Fresh "s") KSharing
            let (e, p, t) = freshExpressionAttributes fresh
            let called = mkFunctionType e p t i o s
            let caller = mkFunctionType e p t (TSeq (DotSeq.SInd (called, irest))) o (TFalse KSharing)
            (qualType [] caller, [], [Syntax.EDo])
        | Syntax.EDecimal d ->
            freshConstWord fresh (freshFloatType fresh d.Size) word
        | Syntax.EInteger i ->
            freshConstWord fresh (freshIntType fresh i.Size) word
        | Syntax.EString _ ->
            freshConstWord fresh (typeCon "String" KData) word
    and inferBlock fresh env stmts =
        match stmts with
        | [] -> (freshNoChange fresh, [], [])
        | Syntax.SLet { Matcher = ps; Body = b } :: ss ->
            let (bTy, bCnstr, bPlc) = inferExpr fresh env b
            let pInfer = List.map (inferPattern fresh) (DotSeq.toList ps)
            let varTypes = List.collect fst pInfer
            let poppedTypes = List.map snd pInfer
            let varEnv = List.fold (fun env vt ->
                extendVar env (fst vt) (freshConstScheme fresh (snd vt))) env varTypes
            let (ssTy, ssCnstr, ssPlc) = inferBlock fresh varEnv ss
            let popped = freshPopped fresh poppedTypes

            let (uniTyL, uniConstrL) = composeWordTypes bTy popped
            let (uniTyR, uniConstrR) = composeWordTypes uniTyL ssTy
            (uniTyR, List.concat [bCnstr; ssCnstr; uniConstrL; uniConstrR],
                Syntax.SLet { Matcher = ps; Body = bPlc } :: ssPlc)
        | Syntax.SLocals _ :: ss -> failwith "Local functions not yet implemented."
        | Syntax.SExpression e :: ss ->
            let (eTy, eCnstr, ePlc) = inferExpr fresh env e
            let (sTy, sCnstr, sPlc) = inferBlock fresh env ss
            let (uniTy, uniConstrs) = composeWordTypes eTy sTy
            (uniTy, append3 eCnstr sCnstr uniConstrs, Syntax.SExpression ePlc :: sPlc)

    let inferTop fresh env expr =
        let (inferred, constrs, expanded) = inferExpr fresh env expr
        let subst = solveAll fresh constrs
        let normalized = qualSubstExn subst inferred
        let reduced = contextReduceExn fresh normalized.Context env
        if isAmbiguousPredicates reduced (typeFree normalized.Head)
        then failwith "Ambiguous predicates"//(AmbiguousPredicates reduced)
        else (qualType reduced normalized.Head, expanded)

    

    let inferFunction fresh env (fn: Syntax.Function) =
        // TODO: add fixed params to env
        let (ty, exp) = inferTop fresh env fn.Body
        let genTy = schemeFromQual ty
        (genTy, { fn with Body = exp })

    let inferRecFuncs fresh env (fns: List<Syntax.Function>) =
        failwith "Recursive function type inference not yet implemented!"
    
    let rec inferDefs fresh env defs exps =
        match defs with
        | [] -> (env, exps)
        | Syntax.DFunc f :: ds ->
            let (ty, exp) = inferFunction fresh env f
            inferDefs fresh (extendVar env f.Name.Name ty) ds (Syntax.DFunc exp :: exps)
        | Syntax.DRecFuncs fs :: ds ->
            let (tys, recExps) = inferRecFuncs fresh env fs
            let newEnv =
                Syntax.declNames (Syntax.DRecFuncs fs)
                |> Syntax.namesToStrings
                |> Seq.zip tys
                |> Seq.fold (fun env nt -> extendVar env (snd nt) (fst nt)) env
            inferDefs fresh newEnv ds (Syntax.DRecFuncs recExps :: exps)
        | d :: ds -> failwith $"Inference for declaration {d} not yet implemented."
    
    let inferProgram prog =
        let fresh = SimpleFresh(0)
        let (env, expanded) = inferDefs fresh Primitives.primTypeEnv prog.Declarations []
        let (mType, mainExpand) = inferTop fresh env prog.Main
        { Declarations = expanded; Main = mainExpand }