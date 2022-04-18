namespace Boba.Core

module Fresh =

    [<Interface>]
    type FreshVars =
        /// Given a prefix, generates a fresh variable name for
        /// the prefix using a number affixed to the name.
        abstract member Fresh : string -> string
        /// Generates `count` fresh variable names
        /// all with the given prefix.
        abstract member FreshN : string -> int -> List<string>

    type SimpleFresh =

        val mutable state: int

        new(s) = { state = s }

        interface FreshVars with
            /// Given a prefix, generates a fresh variable name for
            /// the prefix using a number affixed to the name.
            member this.Fresh prefix =
                let name = $"{prefix}{this.state}"
                this.state <- this.state + 1
                name

            /// Generates `count` fresh variable names
            /// all with the given prefix.
            member this.FreshN prefix count =
                [ for i in 0..count-1 do yield (this :> FreshVars).Fresh prefix ]