namespace Boba.Compiler

module Primitives =

    open Boba.Core.Common
    open Mochi.Core.Instructions

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
        genIntIntConv isize I8
        |> mapUnion fst (genIntIntConv isize U8)
        |> mapUnion fst (genIntIntConv isize I16)
        |> mapUnion fst (genIntIntConv isize U16)
        |> mapUnion fst (genIntIntConv isize I32)
        |> mapUnion fst (genIntIntConv isize U32)
        |> mapUnion fst (genIntIntConv isize I64)
        |> mapUnion fst (genIntIntConv isize U64)
        |> mapUnion fst (genIntFloatConv isize Single)
        |> mapUnion fst (genIntFloatConv isize Double)
    
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
        genBoolIntConv I8
        |> mapUnion fst (genBoolIntConv U8)
        |> mapUnion fst (genBoolIntConv I16)
        |> mapUnion fst (genBoolIntConv U16)
        |> mapUnion fst (genBoolIntConv I32)
        |> mapUnion fst (genBoolIntConv U32)
        |> mapUnion fst (genBoolIntConv I64)
        |> mapUnion fst (genBoolIntConv U64)
        |> mapUnion fst (genBoolFloatConv Single)
        |> mapUnion fst (genBoolFloatConv Double)
        |> mapUnion fst (genIntConv I8)
        |> mapUnion fst (genIntConv U8)
        |> mapUnion fst (genIntConv I16)
        |> mapUnion fst (genIntConv U16)
        |> mapUnion fst (genIntConv I32)
        |> mapUnion fst (genIntConv U32)
        |> mapUnion fst (genIntConv I64)
        |> mapUnion fst (genIntConv U64)
        |> mapUnion fst (genFloatFloatConv Single Double)

    let intPrimMap =
        genIntPrimVar I8
        |> mapUnion fst (genIntPrimVar U8)
        |> mapUnion fst (genIntPrimVar I16)
        |> mapUnion fst (genIntPrimVar U16)
        |> mapUnion fst (genIntPrimVar I32)
        |> mapUnion fst (genIntPrimVar U32)
        |> mapUnion fst (genIntPrimVar I64)
        |> mapUnion fst (genIntPrimVar U64)
        |> mapUnion fst (genIntPrimVar ISize)
        |> mapUnion fst (genIntPrimVar USize)

    let floatPrimMap =
        genFloatPrimvar Single |> mapUnion fst (genFloatPrimvar Double)
    
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

    let allPrimNames = allPrimMap |> Map.toSeq |> Seq.map fst |> List.ofSeq

    let genPrimVar prim =
        if Map.containsKey prim allPrimMap
        then allPrimMap.[prim]
        else failwith $"Primitive '{prim}' not yet implemented."
