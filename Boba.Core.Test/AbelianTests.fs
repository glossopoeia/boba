module AbelianTests

open Xunit
open Boba.Core

[<Fact>]
let ``Match succeed: 0 ~> 0`` () =
    Assert.StrictEqual(
        Some Map.empty,
        Abelian.matchEqns (new Fresh.SimpleFresh(0)) (new Abelian.Equation<string, string>()) (new Abelian.Equation<string, string>()))

[<Fact>]
let ``Match succeed: a ~> b`` () =
    Assert.StrictEqual(
        Some (Map.empty.Add("a", new Abelian.Equation<string, string>("b"))),
        Abelian.matchEqns
            (new Fresh.SimpleFresh(0))
            (new Abelian.Equation<string, string>("a"))
            (new Abelian.Equation<string, string>("b")))

[<Fact>]
let ``Match succeed: A^2 * B^3 ~> B^3 * A^2`` () =
    let constLeft = Map.empty.Add("A", 2).Add("B", 3)
    let constRight = Map.empty.Add("B", 3).Add("A", 2)
    Assert.StrictEqual(
        Some Map.empty,
        Abelian.matchEqns (new Fresh.SimpleFresh(0)) (new Abelian.Equation<string, string>(Map.empty, constLeft)) (new Abelian.Equation<string, string>(Map.empty, constRight)))

[<Fact>]
let ``Match succeed: x^2 * y^1 ~> z^3`` () =
    let leftEqn = Map.empty.Add("x", 2).Add("y", 1)
    let rightEqn = Map.empty.Add("z", 3)
    let matcher =
        Abelian.matchEqns
            (new Fresh.SimpleFresh(0))
            (new Abelian.Equation<string, string>(leftEqn, Map.empty))
            (new Abelian.Equation<string, string>(rightEqn, Map.empty))

    Assert.StrictEqual(
        Some (Map.empty.Add("x", (new Abelian.Equation<string, string>("a0"))).Add("y", new Abelian.Equation<string, string>(Map.empty.Add("a0", -2).Add("z", 3), Map.empty))),
        matcher)

[<Fact>]
let ``Match fail: x^2 ~> x * y`` () =
    let leftEqn = Map.empty.Add("x", 2)
    let rightEqn = Map.empty.Add("x", 1).Add("y", 1)
    Assert.StrictEqual(None, Abelian.matchEqns (new Fresh.SimpleFresh(0)) (new Abelian.Equation<string, string>(leftEqn, Map.empty)) (new Abelian.Equation<string, string>(rightEqn, Map.empty)))

[<Fact>]
let ``Match succeed: x^64 * y^-41 ~> 1`` () =
    let leftEqn = Map.empty.Add("x", 64).Add("y", -41)
    let rightEqn = Map.empty.Add("a", 1)
    let matcher =
        Abelian.matchEqns
            (new Fresh.SimpleFresh(0))
            (new Abelian.Equation<string, string>(leftEqn, Map.empty))
            (new Abelian.Equation<string, string>(rightEqn, Map.empty))

    let expected =
        Some
            (Map.empty
                .Add("x", (new Abelian.Equation<string, string>(Map.empty.Add("a", -16).Add("a6", -41), Map.empty)))
                .Add("y", new Abelian.Equation<string, string>(Map.empty.Add("a", -25).Add("a6", -64), Map.empty)))

    Assert.StrictEqual(expected, matcher)

[<Fact>]
let ``Unify succeed: x^2 * y ~ z^3`` () =
    let leftEqn = Map.empty.Add("x", 2).Add("y", 1)
    let rightEqn = Map.empty.Add("z", 3)
    let unifier =
        Abelian.unify
            (new Fresh.SimpleFresh(0))
            (new Abelian.Equation<string, string>(leftEqn, Map.empty))
            (new Abelian.Equation<string, string>(rightEqn, Map.empty))
    let expected =
        Some
            (Map.empty
                .Add("x", (new Abelian.Equation<string, string>("a0")))
                .Add("y", new Abelian.Equation<string, string>(Map.empty.Add("a0", -2).Add("a2", 3), Map.empty))
                .Add("z", new Abelian.Equation<string, string>("a2")))
    Assert.StrictEqual(expected, unifier)

[<Fact>]
let ``Unify succeed: a ~ b`` () =
    let unifier =
        Abelian.unify
            (new Fresh.SimpleFresh(0))
            (new Abelian.Equation<string, string>(Map.empty.Add("a", 1), Map.empty))
            (new Abelian.Equation<string, string>(Map.empty.Add("b", 1), Map.empty))
    let expected =
        Some (Map.empty
                .Add("a", new Abelian.Equation<string, string>("a1"))
                .Add("b", new Abelian.Equation<string, string>("a1")))
    Assert.StrictEqual(expected, unifier)