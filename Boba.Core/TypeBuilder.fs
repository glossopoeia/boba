namespace Boba.Core

module TypeBuilder =

    open DotSeq
    open Kinds
    open Types

    let mkValueType data sharing =
        typeApp (typeApp (TPrim PrValue) data) sharing
    let valueTypeData ty =
        match ty with
        | TApp (TApp (TPrim PrValue, data), _) -> data
        | _ -> failwith "Could not extract data from value type."
    let valueTypeSharing ty =
        match ty with
        | TApp (TApp (TPrim PrValue, _), sharing) -> sharing
        | _ -> failwith "Could not extract sharing from value type."

    let mkFunctionType effs perms total ins outs sharing =
        typeApp (typeApp (TPrim PrValue) (typeApp (typeApp (typeApp (typeApp (typeApp (TPrim PrFunction) effs) perms) total) ins) outs)) sharing
    let functionTypeEffs ty =
        match ty with
        | TApp (TApp (_, TApp (TApp (TApp (TApp (TApp (_, effs), _), _), _), _)), _) -> effs
        | _ -> failwith "Could not extract effects from function type."
    let functionTypePerms ty =
        match ty with
        | TApp (TApp (_, TApp (TApp (TApp (TApp (TApp (_, _), perms), _), _), _)), _) -> perms
        | _ -> failwith "Could not extract permissions from function type."
    let functionTypeTotal ty =
        match ty with
        | TApp (TApp (_, TApp (TApp (TApp (TApp (TApp (_, _), _), total), _), _)), _) -> total
        | _ -> failwith "Could not extract totality from function type."
    let functionTypeIns ty =
        match ty with
        | TApp (TApp (_, TApp (TApp (TApp (TApp (TApp (_, _), _), _), ins), _)), _) -> ins
        | _ -> failwith "Could not extract input from function type."
    let functionTypeOuts ty =
        match ty with
        | TApp (TApp (_, TApp (TApp (TApp (TApp (TApp (_, _), _), _), _), outs)), _) -> outs
        | _ -> failwith "Could not extract output from function type."
    let functionTypeSharing ty =
        match ty with
        | TApp (TApp (_, TApp (TApp (TApp (TApp (TApp (_, _), _), _), _), _)), sharing) -> sharing
        | _ -> failwith "Could not extract sharing from function type."

    let schemeSharing sch = functionTypeSharing sch.Body.Head

    let mkRowExtend elem row =
        typeApp (typeApp (TRowExtend (typeKindExn elem)) elem) row



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
        
    let signedIntVariants = [I8; I16; I32; I64; ISize]
    let intVariants = [I8; U8; I16; U16; I32; U32; I64; U64; ISize; USize]
    let floatVariants = [Half; Single; Double]
    let bothNumericVariants = List.append (List.map PrInteger intVariants) (List.map PrFloat floatVariants)
    let numericFnSuffix numeric =
        match numeric with
        | PrInteger i -> integerSizeFnSuffix i
        | PrFloat f -> floatSizeFnSuffix f
        | _ -> failwith "Tried to get a suffix of a non-numeric type."

    let numNeg = [for i in bothNumericVariants do yield ("neg-" + numericFnSuffix i, numericUnaryInputUnaryOutputAllSame i)]
    let numAdds = [for i in bothNumericVariants do yield ("add-" + numericFnSuffix i, numericBinaryInputUnaryOutputAllSame i)]
    let numSubs = [for i in bothNumericVariants do yield ("sub-" + numericFnSuffix i, numericBinaryInputUnaryOutputAllSame i)]
    let numMuls = [for i in bothNumericVariants do yield ("mul-" + numericFnSuffix i, mulFnTemplate i)]
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
    let numEq = [for i in bothNumericVariants do yield ("eq-" + numericFnSuffix i, numericComparison i)]
    let numNeq = [for i in bothNumericVariants do yield ("neq-" + numericFnSuffix i, numericComparison i)]
    let numLt = [for i in bothNumericVariants do yield ("lt-" + numericFnSuffix i, numericComparison i)]
    let numLte = [for i in bothNumericVariants do yield ("lte-" + numericFnSuffix i, numericComparison i)]
    let numGt = [for i in bothNumericVariants do yield ("gt-" + numericFnSuffix i, numericComparison i)]
    let numGte = [for i in bothNumericVariants do yield ("gte-" + numericFnSuffix i, numericComparison i)]
    let intSign = [
        for i in signedIntVariants do
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