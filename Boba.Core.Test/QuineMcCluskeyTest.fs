module QuineMcCluskeyTests

open Xunit
open Boba.Core.Boolean
open Boba.Core.QuineMcCluskey

[<Fact>]
let ``Minimize: a => a`` () =
    Assert.StrictEqual(BVar "a", minimize (BVar "a"))

[<Fact>]
let ``Minimize: a & a => a`` () =
    Assert.StrictEqual(BVar "a", minimize (BAnd (BVar "a", BVar "a")))

[<Fact>]
let ``Minimize: a | b | c | d | e => a | b | c | d | e`` () =
    let orVal = BOr (BOr (BOr (BOr (BVar "a", BVar "b"), BVar "c"), BVar "d"), BVar "e")
    Assert.StrictEqual(orVal, minimize orVal)