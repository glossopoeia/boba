namespace Boba.Core.Tests

module AbelianTests =

open NUnit.Framework
open FsCheck.NUnit

[<TestFixture>]
type AbelianMatchingTests () =

    [<Test>]
    member this.IdentityMatches () =
        Assert.IsTrue(
            Abelian.matchEqns (new Fresh.SimpleFresh(0)) (new Abelian.Equation<string, string>()) (new Abelian.Equation<string, string>()) = Some Map.empty)

    [<Test>]
    member this.ConstantMatchOne () =
        let constLeft = Map.empty.Add("A", 2).Add("B", 3)
        let constRight = Map.empty.Add("B", 3).Add("A", 2)
        Assert.IsTrue(
            Some Map.empty = Abelian.matchEqns (new Fresh.SimpleFresh(0)) (new Abelian.Equation<string, string>(Map.empty, constLeft)) (new Abelian.Equation<string, string>(Map.empty, constRight)))

    [<Test>]
    member this.MatchingExampleOne () =
        let leftEqn = Map.empty.Add("x", 2).Add("y", 1)
        let rightEqn = Map.empty.Add("z", 3)
        let matcher =
            Abelian.matchEqns
                (new Fresh.SimpleFresh(0))
                (new Abelian.Equation<string, string>(leftEqn, Map.empty))
                (new Abelian.Equation<string, string>(rightEqn, Map.empty))

        let cond = matcher = Some (Map.empty.Add("x", (new Abelian.Equation<string, string>("a0"))).Add("y", new Abelian.Equation<string, string>(Map.empty.Add("a0", -2).Add("z", 3), Map.empty)))
        Assert.IsTrue(cond)

    [<Test>]
    member this.MatchingExampleTwo () =
        let leftEqn = Map.empty.Add("x", 2)
        let rightEqn = Map.empty.Add("x", 1).Add("y", 1)
        Assert.AreEqual(None, Abelian.matchEqns (new Fresh.SimpleFresh(0)) (new Abelian.Equation<string, string>(leftEqn, Map.empty)) (new Abelian.Equation<string, string>(rightEqn, Map.empty)))

    [<Test>]
    member this.MatchingExampleThree () =
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

        let cond = matcher = expected
        Assert.IsTrue(cond)

[<TestFixture>]
type AbelianUnificationTests () =

    [<Test>]
    member this.Unify