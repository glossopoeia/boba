namespace Boba.Core

module Inference =

    open Common
    open Fresh
    open DotSeq
    open Kinds
    open Types
    open Expression
    open Unification
    open Predicates

    exception AmbiguousPredicates of List<Predicate>

    let simpleUnaryInputUnaryOutputFn i o =
        let e = typeVar "e" (KRow KEffect)
        let p = typeVar "p" (KRow KPermission)
        let t = typeVar "t" KTotality
        let rest = SDot (typeVar "a" KValue, SEnd)
        let i = TSeq (SInd (i, rest))
        let o = TSeq (SInd (o, rest))

        let fnType = mkFunctionType e p t i o (TFalse KSharing)
        { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = qualType [] fnType }

    let simpleBinaryInputUnaryOutputFn i1 i2 o =
        let e = typeVar "e" (KRow KEffect)
        let p = typeVar "p" (KRow KPermission)
        let t = typeVar "t" KTotality
        let rest = SDot (typeVar "a" KValue, SEnd)
        let i = TSeq (SInd (i1, SInd (i2, rest)))
        let o = TSeq (SInd (o, rest))

        let fnType = mkFunctionType e p t i o (TFalse KSharing)
        { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = qualType [] fnType }

    let simpleBinaryInputBinaryOutputFn i1 i2 o1 o2 =
        let e = typeVar "e" (KRow KEffect)
        let p = typeVar "p" (KRow KPermission)
        let t = typeVar "t" KTotality
        let rest = SDot (typeVar "a" KValue, SEnd)
        let i = TSeq (SInd (i1, SInd (i2, rest)))
        let o = TSeq (SInd (o1, SInd (o2, rest)))

        let fnType = mkFunctionType e p t i o (TFalse KSharing)
        { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = qualType [] fnType }

    let numericUnaryInputUnaryOutputAllSame numeric =
        let si = typeVar "s" KSharing
        let so = typeVar "r" KSharing
        let dataType = typeApp (TPrim numeric) (typeVar "u" KUnit)
        simpleBinaryInputUnaryOutputFn (mkValueType dataType si) (mkValueType dataType so)

    let numericBinaryInputUnaryOutputAllSame numeric =
        let sil = typeVar "s" KSharing
        let sir = typeVar "r" KSharing
        let so = typeVar "q" KSharing
        let dataType = typeApp (TPrim numeric) (typeVar "u" KUnit)
        simpleBinaryInputUnaryOutputFn (mkValueType dataType sil) (mkValueType dataType sir) (mkValueType dataType so)

    let numericComparison numeric =
        let sil = typeVar "s" KSharing
        let sir = typeVar "r" KSharing
        let so = typeVar "q" KSharing
        let dataType = typeApp (TPrim numeric) (typeVar "u" KUnit)
        simpleBinaryInputUnaryOutputFn (mkValueType dataType sil) (mkValueType dataType sir) (mkValueType (TPrim PrBool) so)

    let mulFnTemplate numeric =
        let numCon = TPrim numeric
        let num1 = mkValueType (typeApp numCon (typeVar "u" KUnit)) (typeVar "s" KSharing)
        let num2 = mkValueType (typeApp numCon (typeVar "v" KUnit)) (typeVar "r" KSharing)
        let num3 = mkValueType (typeApp numCon (typeMul (typeVar "u" KUnit) (typeVar "v" KUnit))) (typeVar "q" KSharing)
        simpleBinaryInputUnaryOutputFn num1 num2 num3

    let divFnTemplate numeric =
        let numCon = TPrim numeric
        let num1 = mkValueType (typeApp numCon (typeMul (typeVar "u" KUnit) (typeVar "v" KUnit))) (typeVar "s" KSharing)
        let num2 = mkValueType (typeApp numCon (typeVar "u" KUnit)) (typeVar "r" KSharing)
        let num3 = mkValueType (typeApp numCon (typeVar "v" KUnit)) (typeVar "q" KSharing)
        simpleBinaryInputUnaryOutputFn num1 num2 num3

    let divRemFnTemplate numeric =
        let numCon = TPrim (PrInteger numeric)
        let num1 = mkValueType (typeApp numCon (typeMul (typeVar "u" KUnit) (typeVar "v" KUnit))) (typeVar "s" KSharing)
        let num2 = mkValueType (typeApp numCon (typeVar "u" KUnit)) (typeVar "r" KSharing)
        let num3 = mkValueType (typeApp numCon (typeVar "v" KUnit)) (typeVar "q" KSharing)
        let num4 = mkValueType (typeApp numCon (typeMul (typeVar "u" KUnit) (typeVar "v" KUnit))) (typeVar "p" KSharing)
        simpleBinaryInputBinaryOutputFn num1 num2 num3 num4

    let sqrtFnTemplate numeric =
        let numCon = TPrim numeric
        let inp = mkValueType (typeApp numCon (typeExp (typeVar "u" KUnit) 2)) (typeVar "s" KSharing)
        let out1 = mkValueType (typeApp numCon (typeVar "u" KUnit)) (typeVar "r" KSharing)
        let out2 = mkValueType (typeApp numCon (typeVar "u" KUnit)) (typeVar "q" KSharing)
        
        let e = typeVar "e" (KRow KEffect)
        let p = typeVar "p" (KRow KPermission)
        let t = typeVar "t" KTotality
        let rest = SDot (typeVar "a" KValue, SEnd)
        let i = TSeq (SInd (inp, rest))
        let o = TSeq (SInd (out1, SInd (out2, rest)))

        let fnType = mkFunctionType e p t i o (TFalse KSharing)
        { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = qualType [] fnType }
        
    let intVariants = [I8; U8; I16; U16; I32; U32; I64; U64; ISize; USize]
    let floatVariants = [Half; Single; Double]
    let bothNumericVariants = List.append (List.map PrInteger intVariants) (List.map PrFloat floatVariants)
    let numericFnSuffix numeric =
        match numeric with
        | PrInteger i -> integerSizeFnSuffix i
        | PrFloat f -> floatSizeFnSuffix f
        | _ -> failwith "Tried to get a suffix of a non-numeric type."

    let numNeg = [for i in bothNumericVariants do yield ("neg-" + numericFnSuffix i, numericUnaryInputUnaryOutputAllSame i)]
    let intAdds = [for i in bothNumericVariants do yield ("add-" + numericFnSuffix i, numericBinaryInputUnaryOutputAllSame i)]
    let intSubs = [for i in bothNumericVariants do yield ("sub-" + numericFnSuffix i, numericBinaryInputUnaryOutputAllSame i)]
    let intMuls = [for i in bothNumericVariants do yield ("mul-" + numericFnSuffix i, mulFnTemplate i)]
    let intDivRemTs = [for i in intVariants do yield ("divRemT-" + integerSizeFnSuffix i, divRemFnTemplate i)]
    let intDivRemFs = [for i in intVariants do yield ("divRemF-" + integerSizeFnSuffix i, divRemFnTemplate i)]
    let intDivRemEs = [for i in intVariants do yield ("divRemE-" + integerSizeFnSuffix i, divRemFnTemplate i)]
    let floatDiv = [for f in floatVariants do yield ("div-" + floatSizeFnSuffix f, divFnTemplate (PrFloat f))]
    let intOr = [for i in intVariants do yield ("or-" + integerSizeFnSuffix i, numericBinaryInputUnaryOutputAllSame (PrInteger i))]
    let intAnd = [for i in intVariants do yield ("and-" + integerSizeFnSuffix i, numericBinaryInputUnaryOutputAllSame (PrInteger i))]
    let intXor = [for i in intVariants do yield ("xor-" + integerSizeFnSuffix i, numericBinaryInputUnaryOutputAllSame (PrInteger i))]
    let intShl = [for i in intVariants do yield ("shl-" + integerSizeFnSuffix i, mulFnTemplate (PrInteger i))]
    let intAshr = [for i in intVariants do yield ("ashr-" + integerSizeFnSuffix i, numericBinaryInputUnaryOutputAllSame (PrInteger i))]
    let intLshr = [for i in intVariants do yield ("lshr-" + integerSizeFnSuffix i, divFnTemplate (PrInteger i))]
    let intEq = [for i in bothNumericVariants do yield ("eq-" + numericFnSuffix i, numericComparison i)]
    let intNeq = [for i in bothNumericVariants do yield ("neq-" + numericFnSuffix i, numericComparison i)]
    let intLt = [for i in bothNumericVariants do yield ("lt-" + numericFnSuffix i, numericComparison i)]
    let intLte = [for i in bothNumericVariants do yield ("lte-" + numericFnSuffix i, numericComparison i)]
    let intGt = [for i in bothNumericVariants do yield ("gt-" + numericFnSuffix i, numericComparison i)]
    let intGte = [for i in bothNumericVariants do yield ("gte-" + numericFnSuffix i, numericComparison i)]
    let intSign = [
        for i in intVariants do
        yield ("sign-" + integerSizeFnSuffix i,
               simpleUnaryInputUnaryOutputFn
                   (mkValueType (typeApp (TPrim (PrInteger i)) (typeVar "u" KUnit)) (typeVar "s" KSharing))
                   (mkValueType (typeApp (TPrim (PrInteger i)) (TAbelianOne KUnit)) (typeVar "r" KSharing)))]
    let floatSign = [
        for f in floatVariants do
        yield ("sign-" + floatSizeFnSuffix f,
               simpleUnaryInputUnaryOutputFn
                   (mkValueType (typeApp (TPrim (PrFloat f)) (typeVar "u" KUnit)) (typeVar "s" KSharing))
                   (mkValueType (typeApp (TPrim (PrFloat f)) (TAbelianOne KUnit)) (typeVar "r" KSharing)))]
    let floatSqrt = [for f in floatVariants do yield ("sqrt-" + floatSizeFnSuffix f, sqrtFnTemplate (PrFloat f))]



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

    let freshExpressionAttributes (fresh : FreshVars) =
        let e = typeVar (fresh.Fresh "e") (KRow KEffect)
        let p = typeVar (fresh.Fresh "p") (KRow KPermission)
        let t = typeVar (fresh.Fresh "t") KTotality
        (e, p, t)

    let freshConst (fresh : FreshVars) ty =
        let rest = SDot (typeVar (fresh.Fresh "a") KValue, SEnd)
        let s = typeVar (fresh.Fresh "s") KSharing
        let i = TSeq rest
        let o = TSeq (SInd (mkValueType ty s, rest))
        let (e, p, t) = freshExpressionAttributes fresh
        (qualType [] (mkFunctionType e p t i o (TFalse KSharing)), [])

    let sharedClosure env expr =
        List.ofSeq (exprFree expr)
        |> List.map (Environment.lookup env >> Option.map schemeSharing)
        |> List.map Option.toList
        |> List.concat
        |> attrsToDisjunction KSharing

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
        | WDecimal (_, k) -> freshConst fresh (typeApp (TPrim (PrFloat k)) (typeVar (fresh.Fresh "u") KUnit))
        | WInteger (_, k) -> freshConst fresh (typeApp (TPrim (PrInteger k)) (typeVar (fresh.Fresh "u") KUnit))
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
        | WOperator name ->
            match Environment.lookup env name with
            | Some scheme -> (freshQualExn fresh scheme.Quantified scheme.Body, [])
            | None -> failwith $"Could not find operator {name} in the environment"
        | WConstructor name ->
            match Environment.lookup env name with
            | Some scheme -> (freshQualExn fresh scheme.Quantified scheme.Body, [])
            | None -> failwith $"Could not find constructor {name} in the environment"
        | WIdentifier name ->
            match Environment.lookup env name with
            | Some scheme -> (freshQualExn fresh scheme.Quantified scheme.Body, [])
            | None -> failwith $"Could not find identifier {name} in the environment"
        //| WUntag name -> TODO: lookup and invert
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
        | WFunctionLiteral literal ->
            let (inferred, constrs) = inferExpr fresh env literal
            let asValue =
                mkFunctionType
                    (functionTypeEffs inferred.Head)
                    (functionTypePerms inferred.Head)
                    (functionTypeTotal inferred.Head)
                    (functionTypeIns inferred.Head)
                    (functionTypeOuts inferred.Head)
                    (sharedClosure env literal)
            let rest = SDot (typeVar (fresh.Fresh "a") KValue, SEnd)
            let i = TSeq rest
            let o = TSeq (SInd (asValue, rest))
            let (e, p, t) = freshExpressionAttributes fresh
            (qualType inferred.Context (mkFunctionType e p t i o (TFalse KSharing)), constrs)

    let inferTop fresh env expr =
        let (inferred, constrs) = inferExpr fresh env expr
        let subst = solveAll fresh constrs
        let normalized = qualSubstExn subst inferred
        let reduced = contextReduceExn fresh normalized.Context env
        if isAmbiguousPredicates reduced (typeFree normalized.Head)
        then raise (AmbiguousPredicates reduced)
        else qualType reduced normalized.Head
