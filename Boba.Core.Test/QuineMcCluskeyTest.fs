module QuineMcCluskeyTests

open Xunit
open Boba.Core.Boolean

[<Fact>]
let ``Minimize: a => a`` () =
    Assert.StrictEqual(BVar "a", minimize (BVar "a"))

[<Fact>]
let ``Minimize: a & a => a`` () =
    Assert.StrictEqual(BVar "a", minimize (BAnd (BVar "a", BVar "a")))

[<Fact>]
let ``Minimize: b | b => b`` () =
    Assert.StrictEqual(BVar "b", minimize (BOr (BVar "b", BVar "b")))

[<Fact>]
let ``Minimize: a | b | c | d | e => a | b | c | d | e`` () =
    let orVal = BOr (BOr (BOr (BOr (BVar "a", BVar "b"), BVar "c"), BVar "d"), BVar "e")
    Assert.StrictEqual(orVal, minimize orVal)

[<Fact>]
let ``Minimize: a | b | c | d | e | f | g | h => a | b | c | d | e | f | g | h`` () =
    let orVal = BOr (BOr (BOr (BOr (BOr (BOr (BVar "a", BVar "b"), BVar "c"), BVar "d"), BVar "e"), BVar "g"), BVar "h")
    Assert.StrictEqual(orVal, minimize orVal)

[<Fact>]
let ``Minimize: a | (b & c) => `` () =
    let eqn = BOr (BVar "a", BAnd (BVar "b", BVar "c"))
    Assert.StrictEqual(eqn, minimize eqn)

[<Fact>]
let ``Minimize: a... | b => a... | b`` () =
    let eqn = BOr (BDotVar "a", BVar "b")
    Assert.StrictEqual(eqn, minimize eqn)

[<Fact>]
let ``Minimize: a | (b & e) | (b & f) | a | (b & !g) | a => a | (b & e) | (b & f) | (b & !g)`` () =
    let eqn = BOr (BOr (BOr (BOr (BOr (BVar "a", BAnd (BVar "b", BVar "e")), BAnd (BVar "b", BVar "f")), BVar "a"), BAnd (BVar "f", BNot (BVar "g"))), BVar "a")
    let sol = BOr (BOr (BOr (BVar "a", BAnd (BVar "b", BVar "e")), BAnd (BVar "b", BVar "f")), BAnd (BVar "f", BNot (BVar "g")))
    Assert.StrictEqual(sol, minimize eqn)