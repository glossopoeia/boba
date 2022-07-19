namespace Boba.Compiler

module Primitives =

    open Boba.Core.Syntax

    let primDup = WNativeVar "dup"
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
    let primConsList = WNativeVar "cons-list"
    let primSnocList = WNativeVar "snoc-list"
    let primHeadList = WNativeVar "head-list"
    let primTailList = WNativeVar "tail-list"
    let primBreakList = WNativeVar "break-list"
    let primLengthList = WNativeVar "length-list"
    let primIsEmptyList = WCallVar "is-empty-list"

    let primRefGet = WNativeVar "get"

    let primYield = WOperatorVar "yield!"