namespace Boba.Compiler

module Primitives =

    open Boba.Core.Syntax

    let primDup = WCallVar "../prim/core-combinators.dup"
    let primSwap = WCallVar "../prim/core-combinators.swap"
    let primDrop = WCallVar "../prim/core-combinators.drop"
    let primClear = WNativeVar "../prim/core-combinators.clear"
    let primGather = WNativeVar "../prim/core-combinators.gather"
    let primSpread = WNativeVar "../prim/core-combinators.spread"

    let primTrueBool = WNativeVar "../prim/core-boolean.true-bool"
    let primFalseBool = WNativeVar "../prim/core-boolean.false-bool"
    let primNotBool = WNativeVar "../prim/core-boolean.not-bool"
    let primAndBool = WNativeVar "../prim/core-boolean.and-bool"

    let primGreaterINative = WNativeVar "../prim/core-numbers.gt-inative"
    let primLessINative = WNativeVar "../prim/core-numbers.lt-inative"
    let primEqINative = WNativeVar "../prim/core-numbers.eq-inative"

    let primEqSingle = WNativeVar "../prim/core-numbers.eq-single"

    let primNilString = WNativeVar "../prim/core-strings.nil-string"
    let primSnocString = WNativeVar "../prim/core-strings.snoc-string"
    let primHeadString = WNativeVar "../prim/core-strings.head-string"
    let primTailString = WNativeVar "../prim/core-strings.tail-string"
    let primDecodeRuneInString = WNativeVar "../prim/core-strings.decode-rune-in-string"
    let primLengthString = WNativeVar "../prim/core-strings.length-string"
    let primEqString = WNativeVar "../prim/core-strings.eq-string"

    let primNilTuple = WNativeVar "../prim/core-collections.nil-tuple"
    let primConsTuple = WNativeVar "../prim/core-collections.cons-tuple"
    let primHeadTuple = WNativeVar "../prim/core-collections.head-tuple"
    let primTailTuple = WNativeVar "../prim/core-collections.tail-tuple"
    let primBreakTuple = WNativeVar "../prim/core-collections.break-tuple"
    let primLengthTuple = WNativeVar "../prim/core-collections.length-tuple"

    let primNilList = WNativeVar "../prim/core-collections.nil-list"
    let primConsList = WNativeVar "../prim/core-collections.cons-list"
    let primSnocList = WNativeVar "../prim/core-collections.snoc-list"
    let primHeadList = WNativeVar "../prim/core-collections.head-list"
    let primTailList = WNativeVar "../prim/core-collections.tail-list"
    let primBreakList = WNativeVar "../prim/core-collections.break-list"
    let primLengthList = WNativeVar "../prim/core-collections.length-list"
    let primIsEmptyList = WCallVar "../prim/core-collections.is-empty-list"

    let primRefGet = WNativeVar "../prim/core-ref.get"

    let primYield = WOperatorVar "../prim/core-overload.yield!"