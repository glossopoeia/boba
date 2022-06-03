namespace Boba.Compiler

module Primitives =

    open Boba.Core
    open Boba.Core.Common
    open Boba.Core.DotSeq
    open Boba.Core.Kinds
    open Boba.Core.TypeBuilder
    open Mochi.Core
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
    
    let allPrimMap =
        Map.empty
        |> Map.add "dup" [IDup]
        |> Map.add "swap" [ISwap]
        |> Map.add "drop" [IZap]

        |> Map.add "clear" [IClear]
        |> Map.add "gather" [IGather]
        |> Map.add "spread" [ISpread]

        |> Map.add "bool-true" [ITrue]
        |> Map.add "bool-false" [IFalse]

        |> Map.add "nil-list" [IListNil]
        |> Map.add "cons-list" [IListCons]
        |> Map.add "head-list" [IListHead]
        |> Map.add "tail-list" [IListTail]
        |> Map.add "append-list" [IListAppend]

        |> Map.add "nil-tuple" [IListNil]
        |> Map.add "cons-tuple" [IListCons]
        |> Map.add "break-tuple" [IListBreak]
        |> Map.add "head-tuple" [IListHead]
        |> Map.add "tail-tuple" [IListTail]
        |> Map.add "length-tuple" [IListLength]

        |> Map.add "eq-string" [IStringEq]
        |> Map.add "string-concat" [IStringConcat]
        |> Map.add "print" [IPrint]

    let allPrimWordNames = allPrimMap |> Map.toSeq |> Seq.map fst |> List.ofSeq

    let genPrimVar prim =
        if Map.containsKey prim allPrimMap
        then allPrimMap.[prim]
        else failwith $"Primitive '{prim}' not yet implemented."

    

    let spreadType =
        let e = typeVar "e" (KRow KEffect)
        let p = typeVar "p" (KRow KPermission)
        let rest = SDot (typeVar "z" KValue, SEnd)
        let i = TSeq (SInd (mkTupleType rest (shareVar "s"), rest), KValue)
        let o = TSeq (rest, KValue)
        let fnType = mkExpressionType e p totalAttr i o
        { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = unqualType fnType }

    let gatherType =
        let e = typeVar "e" (KRow KEffect)
        let p = typeVar "p" (KRow KPermission)
        let rest = SDot (typeVar "z" KValue, SEnd)
        let i = TSeq (rest, KValue)
        let o = TSeq (SInd (mkTupleType rest (shareVar "s"), rest), KValue)
        let fnType = mkExpressionType e p totalAttr i o
        { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = unqualType fnType }
    
    let clearType =
        let e = typeVar "e" (KRow KEffect)
        let p = typeVar "p" (KRow KPermission)
        let rest = SDot (typeVar "z" KValue, SEnd)
        let i = TSeq (rest, KValue)
        let o = TSeq (SEnd, KValue)
        let fnType = mkExpressionType e p totalAttr i o
        { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = unqualType fnType }

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

    let swapType =
        let low = mkValueType (typeVar "a" KData) (shareVar "s")
        let high = mkValueType (typeVar "b" KData) (shareVar "r")
        simpleBinaryInputBinaryOutputFn high low low high
    
    let zapType =
        let ty = mkValueType (typeVar "a" KData) (shareVar "s")
        simpleUnaryInputNoOutputFn ty



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
        |> addPrimType "swap" swapType
        |> addPrimType "drop" zapType
        |> addPrimType "clear" clearType
        |> addPrimType "gather" gatherType
        |> addPrimType "spread" spreadType
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
        |> addPrimType "nil-tuple"
            (simpleNoInputUnaryOutputFn
                (mkTupleType SEnd (shareVar "s")))
        |> addPrimType "cons-tuple"
            (simpleBinaryInputUnaryOutputFn
                (typeVar "b" KValue)
                (mkTupleType
                    (dot (typeVar "a" KValue) SEnd)
                    (shareVar "s"))
                (mkTupleType
                    (ind (typeVar "b" KValue) (dot (typeVar "a" KValue) SEnd))
                    (shareVar "s")))
        |> addPrimType "string-concat"
            (simpleBinaryInputUnaryOutputFn
                (mkStringValueType (trustVar "v1") (clearVar "cl") (shareVar "s1"))
                (mkStringValueType (trustVar "v2") (clearVar "cr") (shareVar "s2"))
                (mkStringValueType
                    (typeAnd (trustVar "v1") (trustVar "v2"))
                    (typeAnd (clearVar "cl") (clearVar "cr"))
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
