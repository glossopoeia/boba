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

    let primTypes =
        Map.empty
        |> Map.add "Bool" PrBool
        |> Map.add "I8" (PrInteger I8)
        |> Map.add "U8" (PrInteger U8)
        |> Map.add "I16" (PrInteger I16)
        |> Map.add "U16" (PrInteger U16)
        |> Map.add "I32" (PrInteger I32)
        |> Map.add "U32" (PrInteger U32)
        |> Map.add "I64" (PrInteger I64)
        |> Map.add "U64" (PrInteger U64)
        |> Map.add "Single" (PrFloat Single)
        |> Map.add "Double" (PrFloat Double)
        
    let genBoolIntConv isize =
        let sizeSuffix = isize.ToString().ToLower()
        Map.empty
        |> Map.add ("conv-bool-" + sizeSuffix) [IConvBoolInt isize]
        |> Map.add ("conv-" + sizeSuffix + "-bool") [IConvIntBool isize]

    let genBoolFloatConv fsize =
        let sizeSuffix = fsize.ToString().ToLower()
        Map.empty
        |> Map.add ("conv-bool-" + sizeSuffix) [IConvBoolFloat fsize]
        |> Map.add ("conv-" + sizeSuffix + "-bool") [IConvFloatBool fsize]
    
    let genIntIntConv isize1 isize2 =
        let sizeSuffix1 = isize1.ToString().ToLower()
        let sizeSuffix2 = isize2.ToString().ToLower()
        Map.empty
        |> Map.add ("conv-" + sizeSuffix1 + "-" + sizeSuffix2) [IConvIntInt (isize1, isize2)]
        |> Map.add ("conv-" + sizeSuffix2 + "-" + sizeSuffix1) [IConvIntInt (isize2, isize1)]
    
    let genIntFloatConv isize fsize =
        let sizeSuffix1 = isize.ToString().ToLower()
        let sizeSuffix2 = fsize.ToString().ToLower()
        Map.empty
        |> Map.add ("conv-" + sizeSuffix1 + "-" + sizeSuffix2) [IConvIntFloat (isize, fsize)]
        |> Map.add ("conv-" + sizeSuffix2 + "-" + sizeSuffix1) [IConvFloatInt (fsize, isize)]

    let genIntConv isize =
        genIntIntConv isize Instructions.I8
        |> mapUnion fst (genIntIntConv isize Instructions.U8)
        |> mapUnion fst (genIntIntConv isize Instructions.I16)
        |> mapUnion fst (genIntIntConv isize Instructions.U16)
        |> mapUnion fst (genIntIntConv isize Instructions.I32)
        |> mapUnion fst (genIntIntConv isize Instructions.U32)
        |> mapUnion fst (genIntIntConv isize Instructions.I64)
        |> mapUnion fst (genIntIntConv isize Instructions.U64)
        |> mapUnion fst (genIntFloatConv isize Instructions.Single)
        |> mapUnion fst (genIntFloatConv isize Instructions.Double)
    
    let genFloatFloatConv fsize1 fsize2 =
        let sizeSuffix1 = fsize1.ToString().ToLower()
        let sizeSuffix2 = fsize2.ToString().ToLower()
        Map.empty
        |> Map.add ("conv-" + sizeSuffix1 + "-" + sizeSuffix2) [IConvFloatFloat (fsize1, fsize2)]
        |> Map.add ("conv-" + sizeSuffix2 + "-" + sizeSuffix2) [IConvFloatFloat (fsize2, fsize1)]

    let genIntPrimVar isize =
        let sizeSuffix = isize.ToString().ToLower()
        Map.empty
        |> Map.add ("neg-" + sizeSuffix) [IIntNeg isize]
        |> Map.add ("inc-" + sizeSuffix) [IIntInc isize]
        |> Map.add ("dec-" + sizeSuffix) [IIntDec isize]
        |> Map.add ("add-" + sizeSuffix) [IIntAdd isize]
        |> Map.add ("addovf-" + sizeSuffix) [IIntAddOvf isize]
        |> Map.add ("sub-" + sizeSuffix) [IIntSub isize]
        |> Map.add ("subovf-" + sizeSuffix) [IIntSubOvf isize]
        |> Map.add ("mul-" + sizeSuffix) [IIntMul isize]
        |> Map.add ("mulovf-" + sizeSuffix) [IIntMulOvf isize]
        |> Map.add ("divremt-" + sizeSuffix) [IIntDivRemT isize]
        |> Map.add ("divremf-" + sizeSuffix) [IIntDivRemF isize]
        |> Map.add ("divreme-" + sizeSuffix) [IIntDivRemE isize]
        |> Map.add ("or-" + sizeSuffix) [IIntOr isize]
        |> Map.add ("and-" + sizeSuffix) [IIntAnd isize]
        |> Map.add ("xor-" + sizeSuffix) [IIntXor isize]
        |> Map.add ("compl-" + sizeSuffix) [IIntComplement isize]
        |> Map.add ("shl-" + sizeSuffix) [IIntShiftLeft isize]
        |> Map.add ("ashr-" + sizeSuffix) [IIntArithShiftRight isize]
        |> Map.add ("lshr-" + sizeSuffix) [IIntLogicShiftRight isize]
        |> Map.add ("eq-" + sizeSuffix) [IIntEqual isize]
        |> Map.add ("lt-" + sizeSuffix) [IIntLessThan isize]
        |> Map.add ("gt-" + sizeSuffix) [IIntGreaterThan isize]
        |> Map.add ("sign-" + sizeSuffix) [IIntSign isize]

    let genFloatPrimvar fsize =
        let sizeSuffix = fsize.ToString().ToLower()
        Map.empty
        |> Map.add ("neg-" + sizeSuffix) [IFloatNeg fsize]
        |> Map.add ("add-" + sizeSuffix) [IFloatAdd fsize]
        |> Map.add ("sub-" + sizeSuffix) [IFloatSub fsize]
        |> Map.add ("mul-" + sizeSuffix) [IFloatMul fsize]
        |> Map.add ("div-" + sizeSuffix) [IFloatDiv fsize]
        |> Map.add ("eq-" + sizeSuffix) [IFloatEqual fsize]
        |> Map.add ("less-" + sizeSuffix) [IFloatLess fsize]
        |> Map.add ("greater-" + sizeSuffix) [IFloatGreater fsize]
        |> Map.add ("sign-" + sizeSuffix) [IFloatSign fsize]

    let convPrimMap =
        genBoolIntConv Instructions.I8
        |> mapUnion fst (genBoolIntConv Instructions.U8)
        |> mapUnion fst (genBoolIntConv Instructions.I16)
        |> mapUnion fst (genBoolIntConv Instructions.U16)
        |> mapUnion fst (genBoolIntConv Instructions.I32)
        |> mapUnion fst (genBoolIntConv Instructions.U32)
        |> mapUnion fst (genBoolIntConv Instructions.I64)
        |> mapUnion fst (genBoolIntConv Instructions.U64)
        |> mapUnion fst (genBoolFloatConv Instructions.Single)
        |> mapUnion fst (genBoolFloatConv Instructions.Double)
        |> mapUnion fst (genIntConv Instructions.I8)
        |> mapUnion fst (genIntConv Instructions.U8)
        |> mapUnion fst (genIntConv Instructions.I16)
        |> mapUnion fst (genIntConv Instructions.U16)
        |> mapUnion fst (genIntConv Instructions.I32)
        |> mapUnion fst (genIntConv Instructions.U32)
        |> mapUnion fst (genIntConv Instructions.I64)
        |> mapUnion fst (genIntConv Instructions.U64)
        |> mapUnion fst (genFloatFloatConv Instructions.Single Instructions.Double)

    let intPrimMap =
        genIntPrimVar Instructions.I8
        |> mapUnion fst (genIntPrimVar Instructions.U8)
        |> mapUnion fst (genIntPrimVar Instructions.I16)
        |> mapUnion fst (genIntPrimVar Instructions.U16)
        |> mapUnion fst (genIntPrimVar Instructions.I32)
        |> mapUnion fst (genIntPrimVar Instructions.U32)
        |> mapUnion fst (genIntPrimVar Instructions.I64)
        |> mapUnion fst (genIntPrimVar Instructions.U64)
        |> mapUnion fst (genIntPrimVar Instructions.ISize)
        |> mapUnion fst (genIntPrimVar Instructions.USize)

    let floatPrimMap =
        genFloatPrimvar Instructions.Single
        |> mapUnion fst (genFloatPrimvar Instructions.Double)
    
    let allPrimMap =
        Map.empty
        |> Map.add "dup" [IDup]
        |> Map.add "swap" [ISwap]
        |> Map.add "zap" [IZap]

        |> Map.add "new-ref" [INewRef]
        |> Map.add "get-ref" [IGetRef]
        |> Map.add "put-ref" [IPutRef]

        |> Map.add "nil-record" [IEmptyRecord]

        |> Map.add "bool-true" [ITrue]
        |> Map.add "bool-false" [IFalse]
        |> Map.add "and-bool" [IBoolAnd]
        |> Map.add "or-bool" [IBoolOr]
        |> Map.add "not-bool" [IBoolNot]
        |> Map.add "xor-bool" [IBoolXor]
        |> Map.add "eq-bool" [IBoolEq]

        |> Map.add "nil-list" [IListNil]
        |> Map.add "cons-list" [IListCons]
        |> Map.add "head-list" [IListHead]
        |> Map.add "tail-list" [IListTail]
        |> Map.add "append-list" [IListAppend]

        |> Map.add "string-concat" [IStringConcat]
        |> Map.add "print" [IPrint]

        |> mapUnion fst convPrimMap
        |> mapUnion fst intPrimMap
        |> mapUnion fst floatPrimMap

    let allPrimWordNames = allPrimMap |> Map.toSeq |> Seq.map fst |> List.ofSeq

    let genPrimVar prim =
        if Map.containsKey prim allPrimMap
        then allPrimMap.[prim]
        else failwith $"Primitive '{prim}' not yet implemented."

    

    let simpleNoInputUnaryOutputFn o =
        let e = typeVar "e" (KRow KEffect)
        let p = typeVar "p" (KRow KPermission)
        let t = typeVar "t" KTotality
        let rest = SDot (typeVar "z" KValue, SEnd)
        let i = TSeq rest
        let o = TSeq (SInd (o, rest))

        let fnType = mkFunctionValueType e p t i o (TTrue KValidity) (TFalse KSharing)
        { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = qualType [] fnType }

    let simpleUnaryInputUnaryOutputFn i o =
        let e = typeVar "e" (KRow KEffect)
        let p = typeVar "p" (KRow KPermission)
        let t = typeVar "t" KTotality
        let rest = SDot (typeVar "z" KValue, SEnd)
        let i = TSeq (SInd (i, rest))
        let o = TSeq (SInd (o, rest))

        let fnType = mkFunctionValueType e p t i o (TTrue KValidity) (TFalse KSharing)
        { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = qualType [] fnType }

    let simpleBinaryInputUnaryOutputFn i1 i2 o =
        let e = typeVar "e" (KRow KEffect)
        let p = typeVar "p" (KRow KPermission)
        let t = typeVar "t" KTotality
        let rest = SDot (typeVar "z" KValue, SEnd)
        let i = TSeq (SInd (i1, SInd (i2, rest)))
        let o = TSeq (SInd (o, rest))

        let fnType = mkFunctionValueType e p t i o (TTrue KValidity) (TFalse KSharing)
        { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = qualType [] fnType }

    let simpleBinaryInputBinaryOutputFn i1 i2 o1 o2 =
        let e = typeVar "e" (KRow KEffect)
        let p = typeVar "p" (KRow KPermission)
        let t = typeVar "t" KTotality
        let rest = SDot (typeVar "z" KValue, SEnd)
        let i = TSeq (SInd (i1, SInd (i2, rest)))
        let o = TSeq (SInd (o1, SInd (o2, rest)))

        let fnType = mkFunctionValueType e p t i o (TTrue KValidity) (TFalse KSharing)
        { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = qualType [] fnType }

    let boolBinaryInputUnaryOutputAllSame =
        let sil = typeVar "s" KSharing
        let sir = typeVar "r" KSharing
        let so = typeVar "q" KSharing
        let svl = typeVar "v" KValidity
        let svr = typeVar "w" KValidity
        let dataType = TPrim PrBool
        simpleBinaryInputUnaryOutputFn (mkValueType dataType svl sil) (mkValueType dataType svr sir) (mkValueType dataType (TAnd (svl, svr)) so)

    let numericUnaryInputUnaryOutputAllSame numeric =
        let si = typeVar "s" KSharing
        let so = typeVar "r" KSharing
        let sv = typeVar "v" KValidity
        let dataType = typeApp (TPrim numeric) (typeVar "u" KUnit)
        simpleUnaryInputUnaryOutputFn (mkValueType dataType sv si) (mkValueType dataType sv so)

    let numericBinaryInputUnaryOutputAllSame numeric =
        let sil = typeVar "s" KSharing
        let sir = typeVar "r" KSharing
        let so = typeVar "q" KSharing
        let svl = typeVar "v" KValidity
        let svr = typeVar "w" KValidity
        let dataType = typeApp (TPrim numeric) (typeVar "u" KUnit)
        simpleBinaryInputUnaryOutputFn (mkValueType dataType svl sil) (mkValueType dataType svr sir) (mkValueType dataType (TAnd (svl, svr)) so)

    let numericComparison numeric =
        let sil = typeVar "s" KSharing
        let sir = typeVar "r" KSharing
        let so = typeVar "q" KSharing
        let svl = typeVar "v" KValidity
        let svr = typeVar "w" KValidity
        let dataType = typeApp (TPrim numeric) (typeVar "u" KUnit)
        simpleBinaryInputUnaryOutputFn (mkValueType dataType svl sil) (mkValueType dataType svr sir) (mkValueType (TPrim PrBool) (TAnd (svl, svr)) so)

    let mulFnTemplate numeric =
        let numCon = TPrim numeric
        let wValid = typeVar "w" KValidity
        let mValid = typeVar "m" KValidity
        let num1 = mkValueType (typeApp numCon (typeVar "u" KUnit)) wValid (typeVar "s" KSharing)
        let num2 = mkValueType (typeApp numCon (typeVar "v" KUnit)) mValid (typeVar "r" KSharing)
        let num3 = mkValueType (typeApp numCon (typeMul (typeVar "u" KUnit) (typeVar "v" KUnit))) (TAnd (wValid, mValid)) (typeVar "q" KSharing)
        simpleBinaryInputUnaryOutputFn num1 num2 num3

    let divFnTemplate numeric =
        let numCon = TPrim numeric
        let wValid = typeVar "w" KValidity
        let mValid = typeVar "m" KValidity
        let num1 = mkValueType (typeApp numCon (typeMul (typeVar "u" KUnit) (typeVar "v" KUnit))) wValid (typeVar "s" KSharing)
        let num2 = mkValueType (typeApp numCon (typeVar "u" KUnit)) mValid (typeVar "r" KSharing)
        let num3 = mkValueType (typeApp numCon (typeVar "v" KUnit)) (TAnd (wValid, mValid)) (typeVar "q" KSharing)
        simpleBinaryInputUnaryOutputFn num1 num2 num3

    let divRemFnTemplate numeric =
        let numCon = TPrim (PrInteger numeric)
        let wValid = typeVar "w" KValidity
        let mValid = typeVar "m" KValidity
        let num1 = mkValueType (typeApp numCon (typeMul (typeVar "u" KUnit) (typeVar "v" KUnit))) wValid (typeVar "s" KSharing)
        let num2 = mkValueType (typeApp numCon (typeVar "u" KUnit)) mValid (typeVar "r" KSharing)
        let num3 = mkValueType (typeApp numCon (typeVar "v" KUnit)) (TAnd (wValid, mValid)) (typeVar "q" KSharing)
        let num4 = mkValueType (typeApp numCon (typeMul (typeVar "u" KUnit) (typeVar "v" KUnit))) (TAnd (wValid, mValid)) (typeVar "p" KSharing)
        simpleBinaryInputBinaryOutputFn num1 num2 num3 num4

    let sqrtFnTemplate numeric =
        let numCon = TPrim numeric
        let inp = mkValueType (typeApp numCon (typeExp (typeVar "u" KUnit) 2)) (typeVar "v" KValidity) (typeVar "s" KSharing)
        let out1 = mkValueType (typeApp numCon (typeVar "u" KUnit)) (typeVar "v" KValidity) (typeVar "r" KSharing)
        let out2 = mkValueType (typeApp numCon (typeVar "u" KUnit)) (typeVar "v" KValidity) (typeVar "q" KSharing)
        
        let e = typeVar "e" (KRow KEffect)
        let p = typeVar "p" (KRow KPermission)
        let t = typeVar "t" KTotality
        let rest = SDot (typeVar "z" KValue, SEnd)
        let i = TSeq (SInd (inp, rest))
        let o = TSeq (SInd (out1, SInd (out2, rest)))

        let fnType = mkFunctionValueType e p t i o (TTrue KValidity) (TFalse KSharing)
        { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = qualType [] fnType }
        
    let signedIntVariants = [I8; I16; I32; I64; ISize]
    let intVariants = [I8; U8; I16; U16; I32; U32; I64; U64; ISize; USize]
    let floatVariants = [Single; Double]
    let bothNumericVariants = List.append (List.map PrInteger intVariants) (List.map PrFloat floatVariants)
    let numericFnSuffix numeric =
        match numeric with
        | PrInteger i -> integerSizeFnSuffix i
        | PrFloat f -> floatSizeFnSuffix f
        | _ -> failwith "Tried to get a suffix of a non-numeric type."

    let negTypes = [for i in bothNumericVariants do yield ("neg-" + numericFnSuffix i, numericUnaryInputUnaryOutputAllSame i)]
    let addTypes = [for i in bothNumericVariants do yield ("add-" + numericFnSuffix i, numericBinaryInputUnaryOutputAllSame i)]
    let subTypes = [for i in bothNumericVariants do yield ("sub-" + numericFnSuffix i, numericBinaryInputUnaryOutputAllSame i)]
    let mulTypes = [for i in bothNumericVariants do yield ("mul-" + numericFnSuffix i, mulFnTemplate i)]
    let intDivRemTTypes = [for i in intVariants do yield ("divRemT-" + integerSizeFnSuffix i, divRemFnTemplate i)]
    let intDivRemFTypes = [for i in intVariants do yield ("divRemF-" + integerSizeFnSuffix i, divRemFnTemplate i)]
    let intDivRemETypes = [for i in intVariants do yield ("divRemE-" + integerSizeFnSuffix i, divRemFnTemplate i)]
    let floatDivTypes = [for f in floatVariants do yield ("div-" + floatSizeFnSuffix f, divFnTemplate (PrFloat f))]
    let intOrTypes = [for i in intVariants do yield ("or-" + integerSizeFnSuffix i, numericBinaryInputUnaryOutputAllSame (PrInteger i))]
    let intAndTypes = [for i in intVariants do yield ("and-" + integerSizeFnSuffix i, numericBinaryInputUnaryOutputAllSame (PrInteger i))]
    let intXorTypes = [for i in intVariants do yield ("xor-" + integerSizeFnSuffix i, numericBinaryInputUnaryOutputAllSame (PrInteger i))]
    let intShlTypes = [for i in intVariants do yield ("shl-" + integerSizeFnSuffix i, mulFnTemplate (PrInteger i))]
    let intAshrTypes = [for i in intVariants do yield ("ashr-" + integerSizeFnSuffix i, numericBinaryInputUnaryOutputAllSame (PrInteger i))]
    let intLshrTypes = [for i in intVariants do yield ("lshr-" + integerSizeFnSuffix i, divFnTemplate (PrInteger i))]
    let eqNumTypes = [for i in bothNumericVariants do yield ("eq-" + numericFnSuffix i, numericComparison i)]
    let ltNumTypes = [for i in bothNumericVariants do yield ("lt-" + numericFnSuffix i, numericComparison i)]
    let lteNumTypes = [for i in bothNumericVariants do yield ("lte-" + numericFnSuffix i, numericComparison i)]
    let gtNumTypes = [for i in bothNumericVariants do yield ("gt-" + numericFnSuffix i, numericComparison i)]
    let gteNumTypes = [for i in bothNumericVariants do yield ("gte-" + numericFnSuffix i, numericComparison i)]
    let intSignTypes = [
        for i in signedIntVariants do
        yield ("sign-" + integerSizeFnSuffix i,
               simpleUnaryInputUnaryOutputFn
                   (mkValueType (typeApp (TPrim (PrInteger i)) (typeVar "u" KUnit)) (typeVar "v" KValidity) (typeVar "s" KSharing))
                   (mkValueType (typeApp (TPrim (PrInteger i)) (TAbelianOne KUnit)) (typeVar "v" KValidity) (typeVar "r" KSharing)))]
    let floatSignTypes = [
        for f in floatVariants do
        yield ("sign-" + floatSizeFnSuffix f,
               simpleUnaryInputUnaryOutputFn
                   (mkValueType (typeApp (TPrim (PrFloat f)) (typeVar "u" KUnit)) (typeVar "v" KValidity) (typeVar "s" KSharing))
                   (mkValueType (typeApp (TPrim (PrFloat f)) (TAbelianOne KUnit)) (typeVar "v" KValidity) (typeVar "r" KSharing)))]
    let floatSqrtTypes = [for f in floatVariants do yield ("sqrt-" + floatSizeFnSuffix f, sqrtFnTemplate (PrFloat f))]

    let swapType =
        let low = mkValueType (typeVar "z" KData) (typeVar "v" KValidity) (typeVar "s" KSharing)
        let high = mkValueType (typeVar "y" KData) (typeVar "w" KValidity) (typeVar "r" KSharing)
        simpleBinaryInputBinaryOutputFn high low low high



    let addPrimType name ty env =
        Environment.extendVar env name ty

    let addPrimTypes tys env =
        Seq.fold (fun env vt -> Environment.extendVar env (fst vt) (snd vt)) env tys

    let addTypeCtor name env =
        Environment.addTypeCtor env name

    let addTypeCtors ctors env =
        Seq.fold (fun env ct -> Environment.addTypeCtor env (fst ct) (snd ct)) env ctors

    let listTy elem =
        mkListType elem validAttr (TOr (valueTypeSharing elem, shareVar "s2"))

    let primTypeEnv =
        Environment.empty
        |> addPrimTypes negTypes
        |> addPrimTypes addTypes
        |> addPrimTypes subTypes
        |> addPrimTypes mulTypes
        |> addPrimTypes intDivRemTTypes
        |> addPrimTypes intDivRemFTypes
        |> addPrimTypes intDivRemETypes
        |> addPrimTypes floatDivTypes
        |> addPrimTypes intOrTypes
        |> addPrimTypes intAndTypes
        |> addPrimTypes intXorTypes
        |> addPrimTypes eqNumTypes
        |> addPrimTypes ltNumTypes
        |> addPrimTypes lteNumTypes
        |> addPrimTypes gtNumTypes
        |> addPrimTypes gteNumTypes
        |> addPrimTypes intSignTypes
        |> addPrimTypes floatSignTypes
        |> addPrimTypes floatSqrtTypes
        |> addPrimType "and-bool" boolBinaryInputUnaryOutputAllSame
        |> addPrimType "or-bool" boolBinaryInputUnaryOutputAllSame
        |> addPrimType "xor-bool" boolBinaryInputUnaryOutputAllSame
        |> addPrimType "swap" swapType
        |> addPrimType "nil-list"
            (simpleNoInputUnaryOutputFn
                (listTy (mkValueType (typeVar "d" KData) (validityVar "v") (shareVar "s1"))))
        |> addPrimType "cons-list"
            (simpleBinaryInputUnaryOutputFn
                (listTy (mkValueType (typeVar "d" KData) (validityVar "v") (shareVar "s2")))
                (mkValueType (typeVar "d" KData) (validityVar "v") (shareVar "s2"))
                (listTy (mkValueType (typeVar "d" KData) (validityVar "v") (shareVar "s2"))))
        |> addPrimType "append-list"
            (simpleBinaryInputUnaryOutputFn
                (mkListType
                    (mkValueType (typeVar "d" KData) (validityVar "v1") (shareVar "s1"))
                    (validityVar "v2")
                    (TOr (shareVar "s1", shareVar "s2")))
                (mkListType
                    (mkValueType (typeVar "d" KData) (validityVar "v3") (shareVar "s3"))
                    (validityVar "v4")
                    (TOr (shareVar "s3", shareVar "s4")))
                (mkListType
                    (mkValueType (typeVar "d" KData) (TAnd (validityVar "v1", validityVar "v3")) (TOr (shareVar "s1", shareVar "s3")))
                    (TAnd (validityVar "v2", validityVar "v4"))
                    (TOr (shareVar "s1", TOr (shareVar "s2", TOr (shareVar "s3", shareVar "s4"))))))
