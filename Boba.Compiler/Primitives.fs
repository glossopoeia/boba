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
        let sizeSuffix = integerSizeFnSuffix isize
        Map.empty
        |> Map.add ("conv-bool-" + sizeSuffix) [IConvBoolInt isize]
        |> Map.add ("conv-" + sizeSuffix + "-bool") [IConvIntBool isize]

    let genBoolFloatConv fsize =
        let sizeSuffix = floatSizeFnSuffix fsize
        Map.empty
        |> Map.add ("conv-bool-" + sizeSuffix) [IConvBoolFloat fsize]
        |> Map.add ("conv-" + sizeSuffix + "-bool") [IConvFloatBool fsize]
    
    let genIntIntConv isize1 isize2 =
        let sizeSuffix1 = integerSizeFnSuffix isize1
        let sizeSuffix2 = integerSizeFnSuffix isize2
        Map.empty
        |> Map.add ("conv-" + sizeSuffix1 + "-" + sizeSuffix2) [IConvIntInt (isize1, isize2)]
        |> Map.add ("conv-" + sizeSuffix2 + "-" + sizeSuffix1) [IConvIntInt (isize2, isize1)]
    
    let genIntFloatConv isize fsize =
        let sizeSuffix1 = integerSizeFnSuffix isize
        let sizeSuffix2 = floatSizeFnSuffix fsize
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
        let sizeSuffix1 = floatSizeFnSuffix fsize1
        let sizeSuffix2 = floatSizeFnSuffix fsize2
        Map.empty
        |> Map.add ("conv-" + sizeSuffix1 + "-" + sizeSuffix2) [IConvFloatFloat (fsize1, fsize2)]
        |> Map.add ("conv-" + sizeSuffix2 + "-" + sizeSuffix2) [IConvFloatFloat (fsize2, fsize1)]

    let genIntPrimVar isize =
        let sizeSuffix = integerSizeFnSuffix isize
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
        |> Map.add ("divRemT-" + sizeSuffix) [IIntDivRemT isize]
        |> Map.add ("divRemF-" + sizeSuffix) [IIntDivRemF isize]
        |> Map.add ("divRemE-" + sizeSuffix) [IIntDivRemE isize]
        |> Map.add ("or-" + sizeSuffix) [IIntOr isize]
        |> Map.add ("and-" + sizeSuffix) [IIntAnd isize]
        |> Map.add ("xor-" + sizeSuffix) [IIntXor isize]
        |> Map.add ("compl-" + sizeSuffix) [IIntComplement isize]
        |> Map.add ("shl-" + sizeSuffix) [IIntShiftLeft isize]
        |> Map.add ("ashr-" + sizeSuffix) [IIntArithShiftRight isize]
        |> Map.add ("lshr-" + sizeSuffix) [IIntLogicShiftRight isize]
        |> Map.add ("eq-" + sizeSuffix) [IIntEqual isize]
        |> Map.add ("less-" + sizeSuffix) [IIntLessThan isize]
        |> Map.add ("greater-" + sizeSuffix) [IIntGreaterThan isize]
        |> Map.add ("sign-" + sizeSuffix) [IIntSign isize]

    let genFloatPrimvar fsize =
        let sizeSuffix = floatSizeFnSuffix fsize
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
        |> Map.add "drop" [IZap]

        |> Map.add "clear" [IClear]
        |> Map.add "gather" [IGather]
        |> Map.add "spread" [ISpread]

        |> Map.add "new-ref" [INewRef]
        |> Map.add "get-ref" [IGetRef]
        |> Map.add "put-ref" [IPutRef]

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

        |> Map.add "nil-tuple" [IListNil]
        |> Map.add "cons-tuple" [IListCons]
        |> Map.add "break-tuple" [IListBreak]

        |> Map.add "eq-string" [IStringEq]
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

    let boolUnaryInputUnaryOutputAllSame =
        let dataType = TPrim PrBool
        let si = shareVar "s1"
        let so = shareVar "s2"
        simpleUnaryInputUnaryOutputFn (mkValueType dataType si) (mkValueType dataType so)

    let boolBinaryInputUnaryOutputAllSame =
        let sil = shareVar "s"
        let sir = shareVar "r"
        let so = shareVar "so"
        let dataType = TPrim PrBool
        simpleBinaryInputUnaryOutputFn
            (mkValueType dataType sil)
            (mkValueType dataType sir)
            (mkValueType dataType so)

    let numericUnaryInputUnaryOutputAllSame numeric =
        let si = shareVar "s"
        let so = shareVar "r"
        let dataType = typeApp (TPrim numeric) (unitVar "u")
        simpleUnaryInputUnaryOutputFn
            (mkValueType dataType si)
            (mkValueType dataType so)

    let numericBinaryInputUnaryOutputAllSame numeric =
        let sil = shareVar "s"
        let sir = shareVar "r"
        let so = shareVar "q"
        let dataType = typeApp (TPrim numeric) (unitVar "u")
        simpleBinaryInputUnaryOutputFn
            (mkValueType dataType sil)
            (mkValueType dataType sir)
            (mkValueType dataType so)

    let numericComparison numeric =
        let sil = shareVar "s"
        let sir = shareVar "r"
        let so = shareVar "q"
        let dataType = typeApp (TPrim numeric) (unitVar "u")
        simpleBinaryInputUnaryOutputFn
            (mkValueType dataType sil)
            (mkValueType dataType sir)
            (mkValueType (TPrim PrBool) so)

    let conversionFn source target =
        let si = shareVar "s"
        let so = shareVar "r"
        simpleUnaryInputUnaryOutputFn
            (mkValueType source si)
            (mkValueType target so)

    let boolNumericConversion numeric =
        let source = TPrim PrBool
        let target = typeApp (TPrim numeric) (TAbelianOne KUnit)
        conversionFn source target

    let numericBoolConversion numeric =
        let source = typeApp (TPrim numeric) (TAbelianOne KUnit)
        let target = TPrim PrBool
        conversionFn source target

    let numericNumericConversion numeric1 numeric2 =
        let source = typeApp (TPrim numeric1) (unitVar "u")
        let target = typeApp (TPrim numeric2) (unitVar "u")
        conversionFn source target

    let mulFnTemplate numeric =
        let numCon = TPrim numeric
        let num1 = mkValueType (typeApp numCon (unitVar "u")) (shareVar "s")
        let num2 = mkValueType (typeApp numCon (unitVar "v")) (shareVar "r")
        let num3 = mkValueType (typeApp numCon (typeMul (unitVar "u") (unitVar "v"))) (shareVar "q")
        simpleBinaryInputUnaryOutputFn num1 num2 num3

    let divFnTemplate numeric =
        let numCon = TPrim numeric
        let num1 = mkValueType (typeApp numCon (typeMul (unitVar "u") (unitVar "v"))) (shareVar "s")
        let num2 = mkValueType (typeApp numCon (unitVar "u")) (shareVar "r")
        let num3 = mkValueType (typeApp numCon (unitVar "v")) (shareVar "q")
        simpleBinaryInputUnaryOutputFn num1 num2 num3

    let divRemFnTemplate numeric =
        let numCon = TPrim (PrInteger numeric)
        let num1 = mkValueType (typeApp numCon (typeMul (unitVar "u") (unitVar "v"))) (shareVar "s1")
        let num2 = mkValueType (typeApp numCon (unitVar "u")) (shareVar "s2")
        let num3 = mkValueType (typeApp numCon (unitVar "v")) (shareVar "s3")
        let num4 = mkValueType (typeApp numCon (typeMul (unitVar "u") (unitVar "v"))) (shareVar "s4")
        simpleBinaryInputBinaryOutputFn num1 num2 num3 num4

    let sqrtFnTemplate numeric =
        let numCon = TPrim numeric
        let inp = mkValueType (typeApp numCon (typeExp (unitVar "u") 2)) (shareVar "s")
        let out1 = mkValueType (typeApp numCon (unitVar "u")) (shareVar "r")
        let out2 = mkValueType (typeApp numCon (unitVar "u")) (shareVar "q")
        
        let e = typeVar "e" (KRow KEffect)
        let p = typeVar "p" (KRow KPermission)
        let t = typeVar "t" KTotality
        let rest = SDot (typeVar "z" KValue, SEnd)
        let i = TSeq (SInd (inp, rest), KValue)
        let o = TSeq (SInd (out1, SInd (out2, rest)), KValue)

        let fnType = mkExpressionType e p t i o 
        { Quantified = typeFreeWithKinds fnType |> Set.toList; Body = unqualType fnType }
        
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
    let incTypes = [for i in intVariants do yield ("inc-" + integerSizeFnSuffix i, numericUnaryInputUnaryOutputAllSame (PrInteger i))]
    let decTypes = [for i in intVariants do yield ("dec-" + integerSizeFnSuffix i, numericUnaryInputUnaryOutputAllSame (PrInteger i))]
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
    let ltNumTypes = [for i in bothNumericVariants do yield ("less-" + numericFnSuffix i, numericComparison i)]
    let lteNumTypes = [for i in bothNumericVariants do yield ("lte-" + numericFnSuffix i, numericComparison i)]
    let gtNumTypes = [for i in bothNumericVariants do yield ("greater-" + numericFnSuffix i, numericComparison i)]
    let gteNumTypes = [for i in bothNumericVariants do yield ("gte-" + numericFnSuffix i, numericComparison i)]
    let intSignTypes = [
        for i in signedIntVariants do
        yield ("sign-" + integerSizeFnSuffix i,
               simpleUnaryInputUnaryOutputFn
                   (mkValueType (typeApp (TPrim (PrInteger i)) (unitVar "u")) (shareVar "s"))
                   (mkValueType (typeApp (TPrim (PrInteger i)) (TAbelianOne KUnit)) (shareVar "r")))]
    let floatSignTypes = [
        for f in floatVariants do
        yield ("sign-" + floatSizeFnSuffix f,
               simpleUnaryInputUnaryOutputFn
                   (mkValueType (typeApp (TPrim (PrFloat f)) (unitVar "u")) (shareVar "s"))
                   (mkValueType (typeApp (TPrim (PrFloat f)) (TAbelianOne KUnit)) (shareVar "r")))]
    let floatSqrtTypes = [for f in floatVariants do yield ("sqrt-" + floatSizeFnSuffix f, sqrtFnTemplate (PrFloat f))]
    let boolNumericConvTypes = [for f in bothNumericVariants do yield ("conv-bool-" + numericFnSuffix f, boolNumericConversion f)]
    let numericBoolConvTypes = [for f in bothNumericVariants do yield ("conv-" + numericFnSuffix f + "-bool", numericBoolConversion f)]
    let numericNumericConvTypes =
        [for f1 in bothNumericVariants ->
            [for f2 in bothNumericVariants ->
                ("conv-" + numericFnSuffix f1 + "-" + numericFnSuffix f2, numericNumericConversion f1 f2)]]
        |> List.concat

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

    let primTypeEnv =
        Environment.empty
        |> addPrimTypes negTypes
        |> addPrimTypes incTypes
        |> addPrimTypes decTypes
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
        |> addPrimTypes boolNumericConvTypes
        |> addPrimTypes numericBoolConvTypes
        |> addPrimTypes numericNumericConvTypes
        |> addPrimType "not-bool" boolUnaryInputUnaryOutputAllSame
        |> addPrimType "and-bool" boolBinaryInputUnaryOutputAllSame
        |> addPrimType "or-bool" boolBinaryInputUnaryOutputAllSame
        |> addPrimType "xor-bool" boolBinaryInputUnaryOutputAllSame
        |> addPrimType "eq-bool" boolBinaryInputUnaryOutputAllSame
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
            (simpleUnaryInputNoOutputFn
                (mkStringValueType (trustVar "v") clearAttr (shareVar "s")))
