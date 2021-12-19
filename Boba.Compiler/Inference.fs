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

    /// The key inference rule in Boba. Composed words infer their types separately,
    /// then unify the function attributes. The data components unify in a particular
    /// way: the output of the left word unifies with the input of the right word.
    /// This means that the resulting expression has an input of the left word and
    /// and output of the right word, as we would expect from composition.
    /// 
    /// The attributes unify via syntactic equality with no odd replacement rules like
    /// for the values, except for sharing, which does not unify at all since expressions
    /// can't be shared. In truth this means the expression is carrying around a useless
    /// sharing attribute, but it is convenient for expressions to have the same type
    /// construction as functions.
    let composeWordTypes leftType rightType =
        let (le, lp, lt, li, lo) = functionValueTypeComponents leftType.Head
        let (re, rp, rt, ri, ro) = functionValueTypeComponents rightType.Head
        let resTy =
            qualType (List.append leftType.Context rightType.Context)
                (mkFunctionValueType le lp lt li ro
                    (valueTypeValidity leftType.Head)
                    (valueTypeSharing leftType.Head))
        let effConstr = { Left = le; Right = re }
        let permConstr = { Left = lp; Right = rp }
        let totConstr = { Left = lt; Right = rt }
        let insOutsConstr = { Left = lo; Right = ri }
        let validConstr = { Left = valueTypeValidity leftType.Head; Right = valueTypeValidity rightType.Head }
        // assumption: sharing is always false (shared) here, so we don't need to generate a constraint
        (resTy, [effConstr; permConstr; totConstr; insOutsConstr; validConstr])

    // Generates a simple polymorphic expression type of the form (a... -> a...)
    let freshIdentity (fresh : FreshVars) =
        let io = TSeq (freshSequenceVar fresh)
        let (e, p, t) = freshFunctionAttributes fresh
        qualType [] (mkFunctionValueType e p t io io (freshValidityVar fresh) (TFalse KSharing))

    // Generates a simple polymorphic expression type of the form (a... -> a... ty)
    let freshPush (fresh : FreshVars) ty =
        assert (typeKindExn ty = KValue)
        let rest = freshSequenceVar fresh
        let i = TSeq rest
        let o = TSeq (DotSeq.SInd (ty, rest))
        let (e, p, t) = freshFunctionAttributes fresh
        qualType [] (mkFunctionValueType e p t i o (freshValidityVar fresh) (TFalse KSharing))
    
    let freshPopped (fresh: FreshVars) tys =
        let rest = freshSequenceVar fresh
        let o = TSeq rest
        let i = TSeq (DotSeq.append (DotSeq.ofList (List.rev tys)) rest)
        let (e, p, t) = freshFunctionAttributes fresh
        qualType [] (mkFunctionValueType e p t i o (freshValidityVar fresh) (TFalse KSharing))

    /// Generate a type scheme of the form `(a... -> a... ty)` in which all variables are quantified
    /// except those in `ty`.
    let freshPushScheme fresh ty =
        let body = freshPush fresh ty
        let quant = Set.difference (qualFreeWithKinds body) (typeFreeWithKinds ty) |> Set.toList
        { Quantified = quant; Body = body }

    /// Generate a type scheme of the form `(a... -> a... v)` in which the only unquantified variables
    /// are those in `v`.
    let freshVarScheme fresh = freshPushScheme fresh (freshValueVar fresh)

    let freshPushWord (fresh : FreshVars) ty word = (freshPush fresh ty, [], [word])

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
            (vs, freshRefValueType fresh ty)
        | Syntax.PWildcard -> ([], freshValueComponentType fresh)
        | Syntax.PInteger i -> ([], freshIntValueType fresh i.Size)
        | Syntax.PDecimal d -> ([], freshFloatValueType fresh d.Size)
        | Syntax.PString _ -> ([], freshStringValueType fresh)
        | Syntax.PTrue _ -> ([], freshBoolValueType fresh)
        | Syntax.PFalse _ -> ([], freshBoolValueType fresh)

    let rec inferExpr (fresh : FreshVars) env expr =
        let exprInferred = List.map (inferWord fresh env) expr
        let composed =
            List.fold
                (fun (ty, constrs, expanded) (next, newConstrs, nextExpand) ->
                    let (uniTy, uniConstrs) = composeWordTypes ty next
                    (uniTy, append3 constrs newConstrs uniConstrs, List.append expanded nextExpand))
                (freshIdentity fresh, [], [])
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
            let irest = freshSequenceVar fresh
            let i = TSeq irest
            let o = TSeq (freshSequenceVar fresh)
            let s = freshShareVar fresh
            let (e, p, t) = freshFunctionAttributes fresh
            let v = freshValidityVar fresh
            let called = mkFunctionValueType e p t i o v s
            let caller = mkFunctionValueType e p t (TSeq (DotSeq.SInd (called, irest))) o v (TFalse KSharing)
            (qualType [] caller, [], [Syntax.EDo])
        | Syntax.EDecimal d ->
            freshPushWord fresh (freshFloatValueType fresh d.Size) word
        | Syntax.EInteger i ->
            freshPushWord fresh (freshIntValueType fresh i.Size) word
        | Syntax.EString _ ->
            freshPushWord fresh (freshStringValueType fresh) word
    and inferBlock fresh env stmts =
        match stmts with
        | [] -> (freshIdentity fresh, [], [])
        | Syntax.SLet { Matcher = ps; Body = b } :: ss ->
            let (bTy, bCnstr, bPlc) = inferExpr fresh env b
            let pInfer = List.map (inferPattern fresh) (DotSeq.toList ps)
            let varTypes = List.collect fst pInfer
            let poppedTypes = List.map snd pInfer
            let varEnv = List.fold (fun env vt ->
                extendVar env (fst vt) (freshPushScheme fresh (snd vt))) env varTypes
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
    
    let testAmbiguous reduced normalized =
        if isAmbiguousPredicates reduced (typeFree normalized.Head)
        then failwith "Ambiguous predicates"//(AmbiguousPredicates reduced)
        else qualType reduced normalized.Head

    let inferTop fresh env expr =
        try
            let (inferred, constrs, expanded) = inferExpr fresh env expr
            let subst = solveAll fresh constrs
            let normalized = qualSubstExn subst inferred
            let reduced = contextReduceExn fresh normalized.Context env
            (testAmbiguous reduced normalized, expanded)
        with
            | UnifyKindMismatch (t1, t2, k1, k2) -> failwith $"{t1}:{k1} kind mismatch with {t2}:{k2}"
    

    let inferFunction fresh env (fn: Syntax.Function) =
        // TODO: add fixed params to env
        let (ty, exp) = inferTop fresh env fn.Body
        let genTy = schemeFromQual ty
        (genTy, { fn with Body = exp })

    let inferRecFuncs fresh env (fns: List<Syntax.Function>) =
        // TODO: add fixed params to env
        let emptyScheme q = { Quantified = []; Body = q }
        let recEnv = List.fold (fun tenv (fn : Syntax.Function) -> extendRec tenv fn.Name.Name (freshIdentity fresh |> emptyScheme)) env fns
        let infRes = List.map (fun (fn : Syntax.Function) -> inferExpr fresh recEnv fn.Body) fns
        let tys = List.map (fun (t, _, _) -> t) infRes
        let constrs = List.collect (fun (_, c, _) -> c) infRes
        let exps = List.map (fun (_, _, e) -> e) infRes
        let subst = solveAll fresh constrs
        let norms = List.map (qualSubstExn subst) tys
        let reduced = List.map (fun qt -> contextReduceExn fresh qt.Context recEnv) norms
        ((zipWith (uncurry testAmbiguous) reduced norms), exps)
    
    let rec inferDefs fresh env defs exps =
        match defs with
        | [] -> (env, exps)
        | Syntax.DFunc f :: ds ->
            let (ty, exp) = inferFunction fresh env f
            inferDefs fresh (extendVar env f.Name.Name ty) ds (Syntax.DFunc exp :: exps)
        | Syntax.DRecFuncs fs :: ds ->
            let (tys, recExps) = inferRecFuncs fresh env fs
            let recFns = zipWith (fun (fn : Syntax.Function, exp) -> { fn with Body = exp }) fs recExps
            let newEnv =
                Syntax.declNames (Syntax.DRecFuncs fs)
                |> Syntax.namesToStrings
                |> Seq.zip (Seq.map schemeFromQual tys)
                |> Seq.fold (fun env nt -> extendVar env (snd nt) (fst nt)) env
            inferDefs fresh newEnv ds (Syntax.DRecFuncs recFns :: exps)
        | d :: ds -> failwith $"Inference for declaration {d} not yet implemented."
    
    let inferProgram prog =
        let fresh = SimpleFresh(0)
        let (env, expanded) = inferDefs fresh Primitives.primTypeEnv prog.Declarations []
        let (mType, mainExpand) = inferTop fresh env prog.Main
        { Declarations = expanded; Main = mainExpand }