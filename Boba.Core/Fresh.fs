namespace Boba.Core

module Fresh =

    [<Interface>]
    type FreshVars =
        abstract member Fresh : string -> string
        abstract member FreshN : string -> int -> List<string>