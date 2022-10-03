namespace Boba.Compiler

module Primitives =

    open Boba.Core.Syntax
    open Boba.Core.Types

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

    let primEqI32 = WNativeVar "eq-i32"
    let primGreaterINative = WNativeVar "gt-inative"
    let primLessINative = WNativeVar "lt-inative"
    let primEqINative = WNativeVar "eq-inative"

    let primEqSingle = WNativeVar "eq-single"
    let primEqDouble = WNativeVar "eq-double"

    let primNilString = WNativeVar "nil-string"
    let primSnocString = WNativeVar "snoc-string"
    let primHeadString = WNativeVar "head-string"
    let primTailString = WNativeVar "tail-string"
    let primDecodeRuneInString = WNativeVar "decode-rune-in-string"
    let primLengthString = WNativeVar "length-string"
    let primEqString = WNativeVar "eq-string"

    let primNilTuple = WNativeVar "nil-tuple"
    let primConsTuple = WNativeVar "cons-tuple"
    let primHeadTuple = WNativeVar "head-tuple"
    let primTailTuple = WNativeVar "tail-tuple"
    let primBreakTuple = WNativeVar "break-tuple"
    let primLengthTuple = WNativeVar "length-tuple"

    let primNilList = WNativeVar "nil-list"
    let primConsList = WNativeVar "cons-list"
    let primSnocList = WNativeVar "snoc-list"
    let primHeadList = WNativeVar "head-list"
    let primTailList = WNativeVar "tail-list"
    let primBreakList = WNativeVar "break-list"
    let primLengthList = WNativeVar "length-list"
    let primIsEmptyList = WCallVar "is-empty-list"

    let primRefGet = WNativeVar "get"

    let primYield = WOperatorVar "yield!"

    let intEqs =
        Map.empty
        |> Map.add I32 primEqI32
        |> Map.add INative primEqINative
    
    let floatEqs =
        Map.empty
        |> Map.add Single primEqSingle
        |> Map.add Double primEqDouble