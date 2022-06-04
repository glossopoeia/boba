namespace Boba.Compiler

module Primitives =

    open Boba.Core
    open Boba.Core.DotSeq
    open Boba.Core.Kinds
    open Boba.Core.TypeBuilder
    open Boba.Core.Syntax
    open Mochi.Core.Instructions
    open Boba.Core.Types

    let primKinds =
        Map.empty
        |> Map.add "Val" KValue
        |> Map.add "Data" KData
        |> Map.add "Constraint" KConstraint
        |> Map.add "Effect" KEffect
        |> Map.add "Field" KField
        |> Map.add "Permission" KPermission
        |> Map.add "Totality" KTotality

    let primDup = WCallVar "dup"
    let primSwap = WCallVar "swap"
    let primDrop = WCallVar "drop"
    let primClear = WNativeVar "clear"
    let primGather = WNativeVar "gather"
    let primSpread = WNativeVar "spread"

    let primTrueBool = WNativeVar "true-bool"
    let primFalseBool = WNativeVar "false-bool"
    let primNotBool = WNativeVar "not-bool"
    let primAndBool = WNativeVar "and-bool"

    let primGreaterI32 = WNativeVar "gt-i32"
    let primLessI32 = WNativeVar "lt-i32"
    let primEqI32 = WNativeVar "eq-i32"

    let primEqSingle = WNativeVar "eq-single"

    let primEqString = WNativeVar "eq-string"

    let primNilTuple = WNativeVar "nil-tuple"
    let primConsTuple = WNativeVar "cons-tuple"
    let primHeadTuple = WNativeVar "head-tuple"
    let primTailTuple = WNativeVar "tail-tuple"
    let primBreakTuple = WNativeVar "break-tuple"
    let primLengthTuple = WNativeVar "length-tuple"

    let primNilList = WNativeVar "nil-list"
    let primIsEmptyList = WNativeVar "is-empty-list"

    let primRefGet = WNativeVar "get"
    
    let allPrimMap =
        Map.empty
        |> Map.add "nil-list" [IListNil]
        |> Map.add "cons-list" [IListCons]
        |> Map.add "head-list" [IListHead]
        |> Map.add "tail-list" [IListTail]
        |> Map.add "append-list" [IListAppend]

        |> Map.add "print" [IPrint]

    let allPrimWordNames = allPrimMap |> Map.toSeq |> Seq.map fst |> List.ofSeq

    let genPrimVar prim =
        if Map.containsKey prim allPrimMap
        then allPrimMap.[prim]
        else failwith $"Primitive '{prim}' not yet implemented."

    

    let simpleNoInputUnaryOutputFn o =
        let e = typeVar "e" (KRow KEffect)
        let p = typeVar "p" (KRow KPermission)
        let rest = SDot (typeVar "z" KValue, SEnd)
        let i = TSeq (rest, KValue)
        let o = TSeq (SInd (o, rest), KValue)

        let fnType = mkExpressionType e p totalAttr i o
        { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = unqualType fnType }

    let simpleUnaryInputNoOutputFn i =
        let e = typeVar "e" (KRow KEffect)
        let p = typeVar "p" (KRow KPermission)
        let rest = SDot (typeVar "z" KValue, SEnd)
        let i = TSeq (SInd (i, rest), KValue)
        let o = TSeq (rest, KValue)

        let fnType = mkExpressionType e p totalAttr i o
        { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = unqualType fnType }

    let simpleUnaryInputUnaryOutputFn i o =
        let e = typeVar "e" (KRow KEffect)
        let p = typeVar "p" (KRow KPermission)
        let rest = SDot (typeVar "z" KValue, SEnd)
        let i = TSeq (SInd (i, rest), KValue)
        let o = TSeq (SInd (o, rest), KValue)

        let fnType = mkExpressionType e p totalAttr i o
        { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = unqualType fnType }

    let simpleBinaryInputUnaryOutputFn i1 i2 o =
        let e = typeVar "e" (KRow KEffect)
        let p = typeVar "p" (KRow KPermission)
        let rest = SDot (typeVar "z" KValue, SEnd)
        let i = TSeq (SInd (i1, SInd (i2, rest)), KValue)
        let o = TSeq (SInd (o, rest), KValue)

        let fnType = mkExpressionType e p totalAttr i o
        { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = unqualType fnType }

    let simpleBinaryInputBinaryOutputFn i1 i2 o1 o2 =
        let e = typeVar "e" (KRow KEffect)
        let p = typeVar "p" (KRow KPermission)
        let rest = SDot (typeVar "z" KValue, SEnd)
        let i = TSeq (SInd (i1, SInd (i2, rest)), KValue)
        let o = TSeq (SInd (o1, SInd (o2, rest)), KValue)

        let fnType = mkExpressionType e p totalAttr i o
        { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = unqualType fnType }



    let addPrimType name ty env =
        Environment.extendFn env name ty

    let addPrimTypes tys env =
        Seq.fold (fun env vt -> Environment.extendFn env (fst vt) (snd vt)) env tys

    let addTypeCtor name env =
        Environment.addTypeCtor env name

    let addTypeCtors ctors env =
        Seq.fold (fun env ct -> Environment.addTypeCtor env (fst ct) (snd ct)) env ctors
    
    let addUserKind name unify env =
        Environment.addUserKind env name unify
    
    let addUserKinds ks env =
        Map.fold (fun env kn ku -> addUserKind kn ku env) env ks

    let primTypeEnv =
        Environment.empty
        |> addPrimType "nil-list"
            (simpleNoInputUnaryOutputFn
                (mkListType (typeVar "a" KValue) (shareVar "s")))
        |> addPrimType "cons-list"
            (simpleBinaryInputUnaryOutputFn
                (typeVar "a" KValue)
                (mkListType
                    (typeVar "a" KValue)
                    (shareVar "si"))
                (mkListType
                    (typeVar "a" KValue)
                    (shareVar "so")))
        |> addPrimType "append-list"
            (simpleBinaryInputUnaryOutputFn
                (mkListType
                    (typeVar "a" KValue)
                    (shareVar "s1"))
                (mkListType
                    (typeVar "a" KValue)
                    (shareVar "s2"))
                (mkListType
                    (typeVar "a" KValue)
                    (shareVar "s3")))
        |> addPrimType "print"
            ((fun _ ->
                let e = typeVar "e" (KRow KEffect)
                let p = mkPermRowExtend "console" (typeVar "p" (KRow KPermission))
                let rest = SDot (typeVar "z" KValue, SEnd)
                let i = TSeq (SInd (mkStringValueType (trustVar "v") clearAttr (shareVar "s"), rest), KValue)
                let o = TSeq (rest, KValue)

                let fnType = mkExpressionType e p totalAttr i o
                { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = unqualType fnType }
            )())
