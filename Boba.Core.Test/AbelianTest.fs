namespace Boba.Core.Test

open System
open Microsoft.VisualStudio.TestTools.UnitTesting
open Boba.Core

[<TestClass>]
type AbelianTest () =

    [<TestMethod>]
    member this.IdentityMatches () =
        Assert.IsTrue(
            Abelian.matchEqns (new Fresh.SimpleFresh(0)) (new Abelian.Equation<string, string>()) (new Abelian.Equation<string, string>()) = Some Map.empty)

    [<TestMethod>]
    member this.ConstantMatchOne () =
        let constLeft = Map.empty.Add("A", 2).Add("B", 3)
        let constRight = Map.empty.Add("B", 3).Add("A", 2)
        Assert.IsTrue(
            Some Map.empty = Abelian.matchEqns (new Fresh.SimpleFresh(0)) (new Abelian.Equation<string, string>(Map.empty, constLeft)) (new Abelian.Equation<string, string>(Map.empty, constRight)))

    [<TestMethod>]
    member this.SameVariableMatchOne () =
        let varLeft = Map.empty.Add("A", 2).Add("B", 3)
        let varRight = Map.empty.Add("B", 3).Add("A", 2)
        match Abelian.matchEqns (new Fresh.SimpleFresh(0)) (new Abelian.Equation<string, string>(varLeft, Map.empty)) (new Abelian.Equation<string, string>(varRight, Map.empty)) with
        | Some subst -> Assert.IsTrue(Map.empty = subst)
        | None -> Assert.Fail("Expected to generate a solution.")

    [<TestMethod>]
    member this.MatchingExampleOne () =
        let leftEqn = Map.empty.Add("x", 2).Add("y", 1)
        let rightEqn = Map.empty.Add("z", 3)
        let matcher =
            Abelian.matchEqns
                (new Fresh.SimpleFresh(0))
                (new Abelian.Equation<string, string>(leftEqn, Map.empty))
                (new Abelian.Equation<string, string>(rightEqn, Map.empty))

        let cond = matcher = Some (Map.empty.Add("x", (new Abelian.Equation<string, string>("a"))).Add("y", new Abelian.Equation<string, string>(Map.empty.Add("a", -2).Add("z", 3), Map.empty)))
        Assert.IsTrue(cond)