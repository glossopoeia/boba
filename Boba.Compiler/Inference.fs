namespace Boba.Compiler

module Inference =

    open System
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

    let map3 f ls =
        let mapped = List.map f ls
        (List.map (fun (x, _, _) -> x) mapped, List.map (fun (_, x, _) -> x) mapped, List.map (fun (_, _, x) -> x) mapped)

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
    
    let freshResume (fresh: FreshVars) tys outs =
        let i = TSeq (DotSeq.append (DotSeq.ofList (List.rev tys)) (freshSequenceVar fresh))
        let (e, p, t) = freshFunctionAttributes fresh
        qualType [] (mkFunctionValueType e p t i outs (TTrue KValidity) (TFalse KSharing))
    
    let nonSeqPolyPopped (fresh: FreshVars) tys =
        let (e, p, t) = freshFunctionAttributes fresh
        let i = TSeq (DotSeq.ofList (List.rev tys))
        let o = TSeq DotSeq.SEnd
        qualType [] (mkFunctionValueType e p t i o (freshValidityVar fresh) (TFalse KSharing))
    
    /// Generate a type scheme of the form `(a... -> a... ty)` in which all variables are quantified
    /// except those in `ty`.
    let freshPushScheme fresh ty =
        let body = freshPush fresh ty
        let quant = Set.difference (qualFreeWithKinds body) (typeFreeWithKinds ty) |> Set.toList
        { Quantified = quant; Body = body }

    /// Generate a type scheme of the form `(a... -> a... v)` in which the only unquantified variables
    /// are those in `v`.
    let freshVarScheme fresh = freshPushScheme fresh (freshValueComponentType fresh)

    let freshPushWord (fresh : FreshVars) ty word = (freshPush fresh ty, [], [word])

    let freshPoppedScheme fresh tys =
        let body = freshPopped fresh tys
        let tysFree = Seq.map typeFreeWithKinds tys |> Set.unionMany
        let quant = Set.difference (qualFreeWithKinds body) tysFree |> Set.toList
        { Quantified = quant; Body = body }

    /// The sharing attribute on a closure is the disjunction of all of the free variables referenced
    /// by the closure, forcing it to be unique if any of the free variables it references are also unique.
    let sharedClosure env expr =
        List.ofSeq (Boba.Compiler.Syntax.exprFree expr)
        |> List.map (lookup env >> Option.map (fun entry -> schemeSharing entry.Type))
        |> List.collect Option.toList
        |> attrsToDisjunction KSharing

    let getWordEntry env name =
        match lookup env name with
        | Some entry -> entry
        | None -> failwith $"Could not find {name} in the environment"

    /// Here, when we instantiate a type from the type environment, we also do inline dictionary
    /// passing, putting in placeholders for the dictionaries that will get resolved to either a
    /// dictionary parameter or dictionary value during generalization.
    /// More details on this implementation tactic: "Implementing Type Classes", https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.53.3952&rep=rep1&type=pdf
    let instantiateAndAddPlaceholders fresh env name word =
        let entry = getWordEntry env name
        let instantiated = instantiateExn fresh entry.Type
        let replaced = 
            if entry.IsClassMethod
            then 
                [Syntax.EMethodPlaceholder (name, instantiated.Context.Head)]
            elif entry.IsRecursive
            then [Syntax.ERecursivePlaceholder { Name = name; Argument = instantiated.Head }]
            else List.append (List.map Syntax.EOverloadPlaceholder instantiated.Context) [word]
        (instantiated, [], replaced)

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
        | Syntax.PInteger i -> ([], freshIntValueType fresh i.Size (freshValidityVar fresh))
        | Syntax.PDecimal d -> ([], freshFloatValueType fresh d.Size (freshValidityVar fresh))
        | Syntax.PString _ -> ([], freshStringValueType fresh (freshValidityVar fresh))
        | Syntax.PTrue _ -> ([], freshBoolValueType fresh (freshValidityVar fresh))
        | Syntax.PFalse _ -> ([], freshBoolValueType fresh (freshValidityVar fresh))
    
    let extendPushVars fresh env varTypes =
        List.fold (fun env vt -> extendVar env (fst vt) (freshPushScheme fresh (snd vt))) env varTypes

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
        | Syntax.EHandle (ps, hdld, hdlrs, aft) ->
            inferHandle fresh env ps hdld hdlrs aft
        | Syntax.EIf (cond, thenClause, elseClause) ->
            let (infCond, constrsCond, condExpand) = inferExpr fresh env cond
            let (infThen, constrsThen, thenExpand) = inferBlock fresh env thenClause
            let (infElse, constrsElse, elseExpand) = inferBlock fresh env elseClause
            let condTemplate = freshPopped fresh [freshBoolValueType fresh validAttr]
            let thenElseSameConstr = { Left = infThen.Head; Right = infElse.Head }
            let (condJoin, constrsCondJoin) = composeWordTypes infCond condTemplate
            let (infJoin, constrsJoin) = composeWordTypes condJoin infThen

            let constrs = List.concat [constrsCond; constrsThen; constrsElse; constrsJoin; constrsCondJoin; [thenElseSameConstr]]
            infJoin, constrs, [Syntax.EIf (condExpand, thenExpand, elseExpand)]
        | Syntax.EWhile (cond, body) ->
            let (infCond, constrsCond, condExpand) = inferExpr fresh env cond
            let (infBody, constrsBody, bodyExpand) = inferBlock fresh env body
            let condTemplate = freshPopped fresh [freshBoolValueType fresh validAttr]
            let condJoin, constrsCondJoin = composeWordTypes infCond condTemplate
            let bodyJoin, constrsBodyJoin = composeWordTypes condJoin infBody
            let whileJoin, constrsWhileJoin = composeWordTypes bodyJoin condJoin
            let constrs = List.concat [constrsCond; constrsBody; constrsCondJoin; constrsBodyJoin; constrsWhileJoin]
            whileJoin, constrs, [Syntax.EWhile (condExpand, bodyExpand)]
        | Syntax.EFunctionLiteral exp ->
            let (eTy, eCnstrs, ePlc) = inferExpr fresh env exp
            let (ne, np, nt) = freshFunctionAttributes fresh
            let asValue = mkValueType (valueTypeData eTy.Head) (valueTypeValidity eTy.Head) (sharedClosure env exp)
            let rest = freshSequenceVar fresh
            let i = TSeq rest
            let o = TSeq (DotSeq.SInd (asValue, rest))
            let v = freshValidityVar fresh
            (qualType eTy.Context (mkFunctionValueType ne np nt i o v (TFalse KSharing)), eCnstrs, [Syntax.EFunctionLiteral ePlc])
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
        | Syntax.EIdentifier id ->
            instantiateAndAddPlaceholders fresh env id.Name.Name word
        | Syntax.EDecimal d ->
            freshPushWord fresh (freshFloatValueType fresh d.Size validAttr) word
        | Syntax.EInteger i ->
            freshPushWord fresh (freshIntValueType fresh i.Size validAttr) word
        | Syntax.EString _ ->
            freshPushWord fresh (freshStringValueType fresh validAttr) word
        | Syntax.ETrue ->
            freshPushWord fresh (freshBoolValueType fresh validAttr) word
        | Syntax.EFalse ->
            freshPushWord fresh (freshBoolValueType fresh validAttr) word
    and inferBlock fresh env stmts =
        match stmts with
        | [] -> (freshIdentity fresh, [], [])
        | Syntax.SLet { Matcher = ps; Body = b } :: ss ->
            let (bTy, bCnstr, bPlc) = inferExpr fresh env b
            let pInfer = List.map (inferPattern fresh) (DotSeq.toList ps)
            let varTypes = List.collect fst pInfer
            let poppedTypes = List.map snd pInfer
            let varEnv = extendPushVars fresh env varTypes
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
    and inferHandle fresh env hdlParams body handlers after =
        assert (handlers.Length > 0)
        let (hdldTy, hdldCnstrs, hdldPlc) = inferBlock fresh env body
        let hdlrTypeTemplates = List.map (fun (h: Boba.Compiler.Syntax.Handler) -> (getWordEntry env h.Name.Name.Name).Type) handlers

        // get the basic effect row type of the effect
        let exHdlrType = instantiateExn fresh hdlrTypeTemplates.[0]
        let effRow = functionValueTypeEffect exHdlrType.Head
        let effCnstr = { Left = effRow; Right = functionValueTypeEffect hdldTy.Head }
        let effHdldTy = 
            {
                Context = hdldTy.Context;
                Head = updateFunctionValueTypeEffect hdldTy.Head (rowTypeTail effRow)
            }

        let psTypes = List.map (fun (p : Syntax.Name) -> (p.Name, freshValueComponentType fresh)) hdlParams
        let psEnv = extendPushVars fresh env psTypes

        let (aftTy, aftCnstrs, aftPlc) = inferExpr fresh psEnv after
        let hdlResult = functionValueTypeOuts aftTy.Head
        let (hdlrTys, hdlrCnstrs, hdlrPlcs) = map3 (inferHandler fresh psEnv psTypes hdlResult) handlers

        let argPopped = freshPopped fresh (List.map snd psTypes)
        let hdlType, hdlCnstrs = composeWordTypes argPopped effHdldTy
        let finalTy, finalCnstrs = composeWordTypes hdlType aftTy
        let replaced = Syntax.EHandle (hdlParams, hdldPlc, hdlrPlcs, aftPlc)
        finalTy, List.concat [finalCnstrs; hdlCnstrs; List.concat hdlrCnstrs; aftCnstrs; [effCnstr]; hdldCnstrs], [replaced]
    and inferHandler fresh env hdlParams resultTy hdlr =
        // TODO: account for fixed parameters here too
        // TODO: this doesn't account for overloaded dictionary parameters yet
        let psTypes = List.map (fun (p: Syntax.Name) -> (p.Name, freshValueComponentType fresh)) hdlr.Params
        let psEnv = extendPushVars fresh env psTypes
        let resumeTy = freshResume fresh (List.map snd hdlParams) resultTy
        let resEnv = extendVar psEnv "resume" { Quantified = []; Body = resumeTy }

        let (bInf, bCnstrs, bPlc) = inferExpr fresh resEnv hdlr.Body
        let argPopped = freshPopped fresh (List.map snd psTypes)
        let (hdlrTy, hdlrCnstrs) = composeWordTypes argPopped bInf

        let hdlrTemplate = freshResume fresh (List.map snd psTypes) resultTy
        hdlrTy, { Left = hdlrTemplate.Head; Right = hdlrTy.Head } :: List.append hdlrCnstrs bCnstrs, { hdlr with Body = bPlc }

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
        | Syntax.STSeq ts ->
            if DotSeq.length ts = 0
            then
                let seqKind = freshKind fresh
                KSeq seqKind, [{ LeftKind = seqKind; RightKind = KValue }], TSeq DotSeq.SEnd
            else
                let ks = DotSeq.map (kindInfer fresh env) ts
                let seqKind =
                    DotSeq.at 0 ks
                    |> Option.defaultWith (fun () -> failwith "No element in type sequence")
                    |> (fun (k, _, _) -> k)
                let cstrs = DotSeq.map (fun (_, cs, _) -> cs) ks |> DotSeq.fold List.append []
                let allSeqKindsEq = DotSeq.map (fun (k, _, _) -> { LeftKind = seqKind; RightKind = k }) ks |> DotSeq.toList
                // Special constraint for sequences, which must have Value element kind
                let allCstrs = append3 [{ LeftKind = seqKind; RightKind = KValue }] allSeqKindsEq cstrs
                KSeq seqKind, allCstrs, TSeq (DotSeq.map (fun (_, _, t) -> t) ks)
        | Syntax.STApp (l, r) ->
            let (lk, lcstrs, lt) = kindInfer fresh env l
            let (rk, rcstrs, rt) = kindInfer fresh env r
            let ret = freshKind fresh
            ret, append3 [{ LeftKind = lk; RightKind = karrow rk ret }] lcstrs rcstrs, TApp (lt, rt)
    and simpleBinaryCon fresh env l r ctor =
        let (lk, lcstrs, lt) = kindInfer fresh env l
        let (rk, rcstrs, rt) = kindInfer fresh env r
        lk, append3 [{ LeftKind = lk; RightKind = rk }] lcstrs rcstrs, ctor (lt, rt)
    and simpleUnaryCon fresh env b ctor =
        let (k, cstrs, t) = kindInfer fresh env b
        k, cstrs, ctor t

    let kindAnnotateQual fresh env (qual : Syntax.SQualifiedType) =
        let kenv = Syntax.stypeFree qual.SHead |> Set.fold (fun e v -> addTypeCtor e v (freshKind fresh)) env
        try
            let (inf, constraints, ty) = kindInfer fresh kenv qual.SHead
            // TODO: annotate and convert the constraints here too
            let subst = solveKindConstraints constraints
            { Context = []; Head = typeKindSubstExn subst ty }
        with
            | KindUnifyMismatchException (l, r) -> failwith $"{l}:{r} failed to unify."
            
    
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
            | UnifyRigidRigidMismatch (l, r) -> failwith $"{l} cannot unify with {r}"
    

    let inferFunction fresh env (fn: Syntax.Function) =
        // TODO: add fixed params to env
        let (ty, exp) = inferTop fresh env fn.Body
        let genTy = schemeFromQual (simplifyQual ty)
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
                |> Seq.zip (Seq.map (simplifyQual >> schemeFromQual) tys)
                |> Seq.fold (fun env nt -> extendVar env (snd nt) (fst nt)) env
            inferDefs fresh newEnv ds (Syntax.DRecFuncs recFns :: exps)
        | Syntax.DCheck c :: ds ->
            match lookup env c.Name.Name with
            | Some entry ->
                let general = instantiateExn fresh entry.Type
                let matcher = kindAnnotateQual fresh env c.Matcher
                // TODO: also check that the contexts match or are a subset
                if isTypeMatch fresh general.Head matcher.Head
                // TODO: should we continue to use the inferred (more general) type, or restrict it to
                // be the quantified asserted type?
                then inferDefs fresh env ds (Syntax.DCheck c :: exps)
                else failwith $"Type of '{c.Name}' did not match it's assertion.\n{general.Head} <> {matcher.Head}"
            | None -> failwith $"Could not find name '{c.Name}' to check its type."
        | Syntax.DEffect e :: ds ->
            // TODO: fix kind to allow effects with params here
            let effTyEnv = addTypeCtor env e.Name.Name KEffect
            let hdlrTys = List.map (fun (h: Syntax.HandlerTemplate) -> (h.Name.Name, schemeFromQual (kindAnnotateQual fresh effTyEnv h.Type))) e.Handlers
            let effEnv = Seq.fold (fun env nt -> extendVar env (fst nt) (snd nt)) effTyEnv hdlrTys
            inferDefs fresh effEnv ds (Syntax.DEffect e :: exps)
        | d :: ds -> failwith $"Inference for declaration {d} not yet implemented."
    
    let inferProgram prog =
        let fresh = SimpleFresh(0)
        let (env, expanded) = inferDefs fresh Primitives.primTypeEnv prog.Declarations []
        let (mType, mainExpand) = inferTop fresh env prog.Main
        let mainTemplate = freshPush fresh (freshIntValueType fresh I32 (freshValidityVar fresh))
        if isTypeMatch fresh mainTemplate.Head mType.Head
        then { Declarations = expanded; Main = mainExpand }, env
        else failwith $"Main expected to have type {mainTemplate}, but had type {mType}"