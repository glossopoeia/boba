namespace Boba.Core

module Inference =

    open Common
    open Fresh
    open DotSeq
    open Kinds
    open Types
    open TypeBuilder
    open Expression
    open Unification
    open Predicates

    exception AmbiguousPredicates of List<Predicate>

    type TypeTable = Map<string, Option<TypeScheme>>



    let composeWordTypes leftType rightType =
        let resTy =
            qualType (List.append leftType.Context rightType.Context)
                (mkFunctionValueType
                    (functionTypeEffs leftType.Head)
                    (functionTypePerms leftType.Head)
                    (functionTypeTotal leftType.Head)
                    (functionTypeIns leftType.Head)
                    (functionTypeOuts rightType.Head)
                    (valueTypeValidity leftType.Head)
                    (valueTypeSharing leftType.Head))
        let effConstr = { Left = functionTypeEffs leftType.Head; Right = functionTypeEffs rightType.Head }
        let permConstr = { Left = functionTypePerms leftType.Head; Right = functionTypePerms rightType.Head }
        let totConstr = { Left = functionTypeTotal leftType.Head; Right = functionTypeTotal rightType.Head }
        let insOutsConstr = { Left = functionTypeOuts leftType.Head; Right = functionTypeIns rightType.Head }
        let validConstr = { Left = valueTypeValidity leftType.Head; Right = valueTypeValidity rightType.Head }
        // assumption: sharing is always false (shared) here
        (resTy, [effConstr; permConstr; totConstr; insOutsConstr; validConstr])

    let freshConst (fresh : FreshVars) ty word =
        let rest = freshSequenceVar fresh
        let s = freshShareVar fresh
        let vv = freshValidityVar fresh
        let vf = freshValidityVar fresh
        let i = TSeq rest
        let o = TSeq (SInd (mkValueType ty vv s, rest))
        let (e, p, t) = freshFunctionAttributes fresh
        (qualType [] (mkFunctionValueType e p t i o vf (TFalse KSharing)), [], [word])

    /// The sharing attribute on a closure is the disjunction of all of the free variables referenced
    /// by the closure, forcing it to be unique if any of the free variables it references are also unique.
    let sharedClosure env expr =
        List.ofSeq (exprFree expr)
        |> List.map (Environment.lookup env >> Option.map (fun entry -> schemeSharing entry.Type))
        |> List.collect Option.toList
        |> attrsToDisjunction KSharing

    /// Here, when we instantiate a type from the type environment, we also do inline dictionary
    /// passing, putting in placeholders for the dictionaries that will get resolved to either a
    /// dictionary parameter or dictionary value during generalization.
    /// More details on this implementation tactic: "Implementing Type Classes", https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.53.3952&rep=rep1&type=pdf
    let instantiateAndAddPlaceholders fresh env name word =
        match Environment.lookup env name with
        | Some entry ->
            let instantiated = instantiateExn fresh entry.Type
            let replaced = 
                if entry.IsClassMethod
                then 
                    [WMethodPlaceholder (name, instantiated.Context.Head)]
                elif entry.IsRecursive
                then [WRecursivePlaceholder { Name = name; Argument = instantiated.Head }]
                else List.append (List.map WOverloadPlaceholder instantiated.Context) [word]
            (instantiated, [], replaced)
        | None -> failwith $"Could not find {name} in the environment"

    let rec inferExpr (fresh : FreshVars) env expr =
        let io = TSeq (freshSequenceVar fresh)
        let (e, p, t) = freshFunctionAttributes fresh
        let exprInferred = List.map (inferWord fresh env) expr
        let v = freshValidityVar fresh
        let composed =
            List.fold
                (fun (ty, constrs, expanded) (next, newConstrs, nextExpand) ->
                    let (uniTy, uniConstrs) = composeWordTypes ty next
                    (uniTy, append3 constrs newConstrs uniConstrs, List.append expanded nextExpand))
                (qualType [] (mkFunctionValueType e p t io io v (TFalse KSharing)), [], [])
                exprInferred
        composed
    and inferWord fresh env word =
        match word with
        | WStatementBlock expr -> inferExpr fresh env expr
        | WChar _ -> freshConst fresh (typeCon "Char" KData) word
        | WDecimal (_, k) -> freshConst fresh (typeApp (TPrim (PrFloat k)) (typeVar (fresh.Fresh "u") KUnit)) word
        | WInteger (_, k) -> freshConst fresh (typeApp (TPrim (PrInteger k)) (typeVar (fresh.Fresh "u") KUnit)) word
        | WString _ -> freshConst fresh (typeCon "String" KData) word
        | WDo ->
            let irest = freshSequenceVar fresh
            let i = TSeq irest
            let o = TSeq (SDot (typeVar (fresh.Fresh "b") KValue, SEnd))
            let s = freshShareVar fresh
            let v = freshValidityVar fresh
            let (e, p, t) = freshFunctionAttributes fresh
            let called = mkFunctionValueType e p t i o v s
            let caller = mkFunctionValueType e p t (TSeq (SInd (called, irest))) o v (TFalse KSharing)
            (qualType [] caller, [], [WDo])
        | WOperator name -> instantiateAndAddPlaceholders fresh env name word
        | WConstructor name -> instantiateAndAddPlaceholders fresh env name word
        | WIdentifier name -> instantiateAndAddPlaceholders fresh env name word
        //| WUntag name -> TODO: lookup and invert
        | WNewRef ->
            // newref : a... b^u --> a... ref<h,b^u>^u|v
            let rest = typeVar (fresh.Fresh "a") KValue
            let (e, p, t) = freshFunctionAttributes fresh
            let heap = typeVar (fresh.Fresh "h") KHeap
            let value = freshValueComponentType fresh
            let ref = freshRefValueType fresh value
            let st = typeApp (TPrim PrState) heap
            let v = freshValidityVar fresh
            let expr = mkFunctionValueType (mkRowExtend st e) p t (TSeq (SInd (value, SDot (rest, SEnd)))) (TSeq (SInd (ref, SDot (rest, SEnd)))) v (TFalse KSharing)
            (qualType [] expr, [], [WNewRef])
        | WGetRef ->
            // getref : a... ref<h,b^u>^u|v --> a... b^u
            let rest = typeVar (fresh.Fresh "a") KValue
            let (e, p, t) = freshFunctionAttributes fresh
            let heap = typeVar (fresh.Fresh "h") KHeap
            let value = freshValueComponentType fresh
            let ref = freshRefValueType fresh value
            let st = typeApp (TPrim PrState) heap
            let expr = mkFunctionValueType (mkRowExtend st e) p t (TSeq (SInd (ref, SDot (rest, SEnd)))) (TSeq (SInd (value, SDot (rest, SEnd)))) (TTrue KValidity) (TFalse KSharing)
            (qualType [] expr, [], [WGetRef])
        | WPutRef ->
            // putref : a... ref<h,b^u>^u|v b^w --> a... ref<h,b^w>^w|v
            let rest = typeVar (fresh.Fresh "a") KValue
            let (e, p, t) = freshFunctionAttributes fresh
            let heap = typeVar (fresh.Fresh "h") KHeap
            let oldValue = freshValueComponentType fresh
            let newValue = freshValueComponentType fresh
            let oldRef = freshRefValueType fresh oldValue
            let newRef = freshRefValueType fresh newValue
            let st = typeApp (TPrim PrState) heap
            let expr = mkFunctionValueType (mkRowExtend st e) p t (TSeq (SInd (newValue, (SInd (oldRef, SDot (rest, SEnd)))))) (TSeq (SInd (newRef, SDot (rest, SEnd)))) (TTrue KValidity) (TFalse KSharing)
            (qualType [] expr, [], [WPutRef])
        | WModifyRef ->
            // modifyref : a... ref<h,b^u>^u|v (a... b^u --> c... d^w) --> c... ref<h,b^w>^w|v
            let oldRest = typeVar (fresh.Fresh "a") KValue
            let newRest = typeVar (fresh.Fresh "b") KValue
            let (e, p, t) = freshFunctionAttributes fresh
            let heap = typeVar (fresh.Fresh "h") KHeap
            let fnShare = typeVar (fresh.Fresh "s") KSharing
            let oldValue = freshValueComponentType fresh
            let newValue = freshValueComponentType fresh
            let oldRef = freshRefValueType fresh oldValue
            let newRef = freshRefValueType fresh newValue
            let st = typeApp (TPrim PrState) heap
            let subFn = mkFunctionValueType e p t (TSeq (SInd (oldValue, SDot (oldRest, SEnd)))) (TSeq (SInd (newValue, SDot (newRest, SEnd)))) (TTrue KValidity) fnShare
            let expr = mkFunctionValueType (mkRowExtend st e) p t (TSeq (SInd (subFn, (SInd (oldRef, SDot (oldRest, SEnd)))))) (TSeq (SInd (newRef, SDot (newRest, SEnd)))) (TTrue KValidity) (TFalse KSharing)
            (qualType [] expr, [], [WModifyRef])
        | WWithState e ->
            // need to do some 'lightweight' generalization here to remove the heap type
            // we have to verify that it is not free in the environment so that we can
            // soundly remove it from the list of effects in the inferred expressions
            let (inferred, constrs, expanded) = inferExpr fresh env e
            let subst = solveAll fresh constrs
            let solved = qualSubstExn subst inferred

            // we filter out the first state eff, since it is the most deeply nested if there are multiple
            let effRow = typeToRow (functionTypeEffs solved.Head)
            let leftOfEff = List.takeWhile (fun e -> rowElementHead e <> (TPrim PrState)) effRow.Elements
            let eff = List.skipWhile (fun e -> rowElementHead e <> (TPrim PrState)) effRow.Elements |> List.head
            let rightOfEff = List.skipWhile (fun e -> rowElementHead e <> (TPrim PrState)) effRow.Elements |> List.skip 1

            // TODO: apply substitution to environment and check for free variable here

            let newRow = List.append leftOfEff rightOfEff
            let newType =
                qualType solved.Context
                    (mkFunctionValueType
                        (rowToType { Elements = newRow; RowEnd = effRow.RowEnd; ElementKind = effRow.ElementKind })
                        (functionTypePerms solved.Head)
                        (functionTypeTotal solved.Head)
                        (functionTypeIns solved.Head)
                        (functionTypeOuts solved.Head)
                        (valueTypeSharing solved.Head)
                        (valueTypeSharing solved.Head))
            (newType, constrs, [WWithState expanded])
        | WIf (thenClause, elseClause) ->
            let (infThen, constrsThen, thenExpand) = inferExpr fresh env thenClause
            let (infElse, constrsElse, elseExpand) = inferExpr fresh env elseClause
            let rest = freshSequenceVar fresh
            let i = TSeq (SInd (freshBoolValueType fresh, rest))
            let o = TSeq rest
            let (e, p, t) = freshFunctionAttributes fresh
            let start = mkFunctionValueType e p t i o (TTrue KValidity) (TFalse KSharing)
            let matchIns = { Left = functionTypeIns infThen.Head; Right = functionTypeIns infElse.Head }
            let matchOuts = { Left = functionTypeOuts infThen.Head; Right = functionTypeOuts infElse.Head }
            let matchStartThen = { Left = functionTypeOuts start; Right = functionTypeIns infThen.Head }
            let matchStartElse = { Left = functionTypeOuts start; Right = functionTypeIns infElse.Head }
            let final = mkFunctionValueType e p t i (functionTypeOuts infThen.Head) (TTrue KValidity) (TFalse KSharing)
            (qualType (List.append infThen.Context infElse.Context) final,
             append3 constrsThen constrsElse [matchIns; matchOuts; matchStartThen; matchStartElse],
             [WIf (thenExpand, elseExpand)])
        | WFunctionLiteral literal ->
            let (inferred, constrs, expanded) = inferExpr fresh env literal
            let asValue =
                mkFunctionValueType
                    (functionTypeEffs inferred.Head)
                    (functionTypePerms inferred.Head)
                    (functionTypeTotal inferred.Head)
                    (functionTypeIns inferred.Head)
                    (functionTypeOuts inferred.Head)
                    (valueTypeValidity inferred.Head)
                    (sharedClosure env literal)
            let rest = freshSequenceVar fresh
            let i = TSeq rest
            let o = TSeq (SInd (asValue, rest))
            let (e, p, t) = freshFunctionAttributes fresh
            (qualType inferred.Context (mkFunctionValueType e p t i o (TTrue KValidity) (TFalse KSharing)), constrs, [WFunctionLiteral expanded])

    let inferTop fresh env expr =
        let (inferred, constrs, expanded) = inferExpr fresh env expr
        let subst = solveAll fresh constrs
        let normalized = qualSubstExn subst inferred
        let reduced = contextReduceExn fresh normalized.Context env
        if isAmbiguousPredicates reduced (typeFree normalized.Head)
        then raise (AmbiguousPredicates reduced)
        else (qualType reduced normalized.Head, expanded)

    let addDictionaryParameters (context : List<Predicate>) expr =
        if List.isEmpty context
        then expr
        else [WVars ([for c in context do yield $"${c.Name}_{c.Argument}"], expr)]

    let resolveMethodPlaceholder context subst env method param =
        match Environment.lookupClassByMethod env method with
        | Some tc ->
            match Map.tryFind param subst with
            | Some (TVar (n, k)) -> [WIdentifier $"${tc}_{param}"; WSelection method; WDo]

            | Some _ -> failwith "Not yet implemented"

            | None -> failwith $"Could not resolve method placeholder {method}, not associated with a substitution."
        | None -> failwith $"Cloud not resolve method placeholder '{method}', no typeclass found."

    let rec resolvePlaceholdersExpr context subst env expr =
        List.collect (resolvePlaceholdersWord context subst env) expr
    and resolvePlaceholdersWord context subst env word =
        match word with
        | WStatementBlock e -> [WStatementBlock (resolvePlaceholdersExpr context subst env e)]
        | WMethodPlaceholder (method, param) -> resolveMethodPlaceholder context subst env method param

