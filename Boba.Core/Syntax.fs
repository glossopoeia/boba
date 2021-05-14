namespace Boba.Core

module Syntax =

    open Types

    type Word =
        | WDo
        | WString of string
        | WInteger of string * IntegerSize
        | WDecimal of string * FloatSize
        | WChar of char
    and Expression = List<Word>