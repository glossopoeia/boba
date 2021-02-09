namespace Boba.Core

module Fresh =

    [<Interface>]
    type FreshVars =
        abstract member Fresh : string -> string
        abstract member FreshN : string -> int -> List<string>

    type SimpleFresh =

        val mutable state: int

        new(s) = { state = s }

        interface FreshVars with
            member this.Fresh prefix =
                let name = $"{prefix}{this.state}"
                this.state <- this.state + 1
                name

            member this.FreshN prefix count =
                [ for i in 0..count do yield (this :> FreshVars).Fresh prefix ]