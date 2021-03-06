namespace Boba.Core

module Inference =

    open Common
    open Fresh
    open DotSeq
    open Kinds
    open Types
    open Expression
    open Unification

    let anyShared expr = true

    let freshExpressionAttributes (fresh : FreshVars) =
        let e = typeVar (fresh.Fresh "e") (KRow KEffect)
        let p = typeVar (fresh.Fresh "p") (KRow KPermission)
        let t = typeVar (fresh.Fresh "t") KTotality
        (e, p, t)

    let composeWords leftType rightType =
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

    let freshConst (fresh : FreshVars) ty =
        let rest = SDot (typeVar (fresh.Fresh "a") KValue, SEnd)
        let s = typeVar (fresh.Fresh "s") KSharing
        let i = TSeq rest
        let o = TSeq (SInd (mkValueType ty s, rest))
        let (e, p, t) = freshExpressionAttributes fresh
        (qualType [] (mkFunctionType e p t i o (TFalse KSharing)), [])

    let rec inferExpr (fresh : FreshVars) env expr =
        let io = TSeq (SDot (typeVar (fresh.Fresh "a") KValue, SEnd))
        let (e, p, t) = freshExpressionAttributes fresh
        let wordInferred = List.map (inferWord fresh env) expr
        let unified =
            List.fold
                (fun (ty, constrs) (next, newConstrs) ->
                    let (uniTy, uniConstrs) = composeWords ty next
                    (uniTy, append3 constrs newConstrs uniConstrs))
                (qualType [] (mkFunctionType e p t io io (TFalse KSharing)), [])
                wordInferred
        unified
    and inferWord fresh env word =
        match word with
        | WStatementBlock expr -> inferExpr fresh env expr
        | WChar _ -> freshConst fresh (typeCon "Char" KData)
        | WDecimal _ -> freshConst fresh (typeApp (TPrim PrFloat32) (typeVar (fresh.Fresh "u") KUnit))
        | WInteger _ -> freshConst fresh (typeApp (TPrim PrInt32) (typeVar (fresh.Fresh "u") KUnit))
        | WString _ -> freshConst fresh (typeCon "String" KData)
        | WDo ->
            let irest = SDot (typeVar (fresh.Fresh "a") KValue, SEnd)
            let i = TSeq irest
            let o = TSeq (SDot (typeVar (fresh.Fresh "b") KValue, SEnd))
            let s = typeVar (fresh.Fresh "s") KSharing
            let (e, p, t) = freshExpressionAttributes fresh
            let called = mkFunctionType e p t i o s
            let caller = mkFunctionType e p t (TSeq (SInd (called, irest))) o (TFalse KSharing)
            (qualType [] caller, [])
        //| WOperator name -> TODO: lookup
        //| WConstructor name -> TODO: lookup
        //| WIdentifier name -> TODO: lookup
        //| WUntag name -> TODO: lookup
        | WNewRef ->
            // newref : a... b^u --> a... ref<h,b^u>^u|v
            let rest = typeVar (fresh.Fresh "a") KValue
            let (e, p, t) = freshExpressionAttributes fresh
            let heap = typeVar (fresh.Fresh "h") KHeap
            let valueShare = typeVar (fresh.Fresh "s") KSharing
            let refShare = typeVar (fresh.Fresh "s") KSharing
            let value = mkValueType (typeVar (fresh.Fresh "t") KData) valueShare
            let ref = mkValueType (typeApp (typeApp (TPrim PrRef) heap) value) (TOr (valueShare, refShare))
            let st = typeApp (TPrim PrState) heap
            let expr = mkFunctionType (mkRowExtend st e) p t (TSeq (SInd (value, SDot (rest, SEnd)))) (TSeq (SInd (ref, SDot (rest, SEnd)))) (TFalse KSharing)
            (qualType [] expr, [])
        | WGetRef ->
            // getref : a... ref<h,b^u>^u|v --> a... b^u
            let rest = typeVar (fresh.Fresh "a") KValue
            let (e, p, t) = freshExpressionAttributes fresh
            let heap = typeVar (fresh.Fresh "h") KHeap
            let valueShare = typeVar (fresh.Fresh "s") KSharing
            let refShare = typeVar (fresh.Fresh "s") KSharing
            let value = mkValueType (typeVar (fresh.Fresh "t") KData) valueShare
            let ref = mkValueType (typeApp (typeApp (TPrim PrRef) heap) value) (TOr (valueShare, refShare))
            let st = typeApp (TPrim PrState) heap
            let expr = mkFunctionType (mkRowExtend st e) p t (TSeq (SInd (ref, SDot (rest, SEnd)))) (TSeq (SInd (value, SDot (rest, SEnd)))) (TFalse KSharing)
            (qualType [] expr, [])
        | WPutRef ->
            // putref : a... ref<h,b^u>^u|v b^w --> a... ref<h,b^w>^w|v
            let rest = typeVar (fresh.Fresh "a") KValue
            let (e, p, t) = freshExpressionAttributes fresh
            let heap = typeVar (fresh.Fresh "h") KHeap
            let oldValueShare = typeVar (fresh.Fresh "s") KSharing
            let newValueShare = typeVar (fresh.Fresh "s") KSharing
            let refShare = typeVar (fresh.Fresh "s") KSharing
            let oldValue = mkValueType (typeVar (fresh.Fresh "t") KData) oldValueShare
            let newValue = mkValueType (typeVar (fresh.Fresh "t") KData) newValueShare
            let oldRef = mkValueType (typeApp (typeApp (TPrim PrRef) heap) oldValue) (TOr (oldValueShare, refShare))
            let newRef = mkValueType (typeApp (typeApp (TPrim PrRef) heap) newValue) (TOr (newValueShare, refShare))
            let st = typeApp (TPrim PrState) heap
            let expr = mkFunctionType (mkRowExtend st e) p t (TSeq (SInd (newValue, (SInd (oldRef, SDot (rest, SEnd)))))) (TSeq (SInd (newRef, SDot (rest, SEnd)))) (TFalse KSharing)
            (qualType [] expr, [])
        | WModifyRef ->
            // modifyref : a... ref<h,b^u>^u|v (a... b^u --> c... d^w) --> c... ref<h,b^w>^w|v
            let oldRest = typeVar (fresh.Fresh "a") KValue
            let newRest = typeVar (fresh.Fresh "b") KValue
            let (e, p, t) = freshExpressionAttributes fresh
            let heap = typeVar (fresh.Fresh "h") KHeap
            let oldValueShare = typeVar (fresh.Fresh "s") KSharing
            let newValueShare = typeVar (fresh.Fresh "s") KSharing
            let refShare = typeVar (fresh.Fresh "s") KSharing
            let fnShare = typeVar (fresh.Fresh "s") KSharing
            let oldValue = mkValueType (typeVar (fresh.Fresh "t") KData) oldValueShare
            let newValue = mkValueType (typeVar (fresh.Fresh "t") KData) newValueShare
            let oldRef = mkValueType (typeApp (typeApp (TPrim PrRef) heap) oldValue) (TOr (oldValueShare, refShare))
            let newRef = mkValueType (typeApp (typeApp (TPrim PrRef) heap) newValue) (TOr (newValueShare, refShare))
            let st = typeApp (TPrim PrState) heap
            let subFn = mkFunctionType e p t (TSeq (SInd (oldValue, SDot (oldRest, SEnd)))) (TSeq (SInd (newValue, SDot (newRest, SEnd)))) fnShare
            let expr = mkFunctionType (mkRowExtend st e) p t (TSeq (SInd (subFn, (SInd (oldRef, SDot (oldRest, SEnd)))))) (TSeq (SInd (newRef, SDot (newRest, SEnd)))) (TFalse KSharing)
            (qualType [] expr, [])
        | WWithState w ->
            // need to do some 'lightweight' generalization here to remove the heap type
            // we have to verify that it is not free in the environment so that we can
            // soundly remove it from the list of effects in the inferred expressions
            let (inferred, constrs) = inferWord fresh env w
            let subst = solveAll fresh constrs
            let solved = qualSubstExn subst inferred

            // we filter the first state eff out, since it is the most deeply nested if there are multiple
            let effRow = typeToRow (functionTypeEffs solved.Head)
            let leftOfEff = List.takeWhile (fun e -> not (rowElementHead e = (TPrim PrState))) effRow.Elements
            let eff = List.skipWhile (fun e -> not (rowElementHead e = (TPrim PrState))) effRow.Elements |> List.head
            let rightOfEff = List.skipWhile (fun e -> not (rowElementHead e = (TPrim PrState))) effRow.Elements |> List.skip 1

            // TODO: apply substitution to environment and check for free variable here

            let newRow = List.append leftOfEff rightOfEff
            let newType =
                qualType solved.Context
                    (mkFunctionType
                        (rowToType { Elements = newRow; RowEnd = effRow.RowEnd; ElementKind = effRow.ElementKind })
                        (functionTypePerms solved.Head)
                        (functionTypeTotal solved.Head)
                        (functionTypeIns solved.Head)
                        (functionTypeOuts solved.Head)
                        (functionTypeSharing solved.Head))
            (newType, constrs)
        | WIf (thenClause, elseClause) ->
            let (infThen, constrsThen) = inferExpr fresh env thenClause
            let (infElse, constrsElse) = inferExpr fresh env elseClause
            let rest = SDot (typeVar (fresh.Fresh "a") KValue, SEnd)
            let s = typeVar (fresh.Fresh "s") KSharing
            let i = TSeq (SInd (mkValueType (TPrim PrBool) s, rest))
            let o = TSeq rest
            let (e, p, t) = freshExpressionAttributes fresh
            let start = mkFunctionType e p t i o (TFalse KSharing)
            let matchIns = { Left = functionTypeIns infThen.Head; Right = functionTypeIns infElse.Head }
            let matchOuts = { Left = functionTypeOuts infThen.Head; Right = functionTypeOuts infElse.Head }
            let matchStartThen = { Left = functionTypeOuts start; Right = functionTypeIns infThen.Head }
            let matchStartElse = { Left = functionTypeOuts start; Right = functionTypeIns infElse.Head }
            let final = mkFunctionType e p t i (functionTypeOuts infThen.Head) (TFalse KSharing)
            (qualType (List.append infThen.Context infElse.Context) final, append3 constrsThen constrsElse [matchIns; matchOuts; matchStartThen; matchStartElse])

    let inferTop fresh env expr =
        let (inferred, constrs) = inferExpr fresh env expr
        let subst = solveAll fresh constrs
        qualSubstExn subst inferred
