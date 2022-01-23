module DotSeqTests

open Xunit
open Boba.Core.DotSeq

[<Fact>]
let ``DotSeq.ofList maintains list order`` () =
    Assert.StrictEqual(ind 1 (ind 2 (ind 3 SEnd)), ofList [1;2;3])

[<Fact>]
let ``DotSeq.toList maintains list order`` () =
    Assert.StrictEqual(toList (ind 1 (ind 2 (ind 3 SEnd))), [1;2;3])