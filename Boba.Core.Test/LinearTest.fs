namespace Boba.Core.Test

open System
open Microsoft.VisualStudio.TestTools.UnitTesting
open Boba.Core

[<TestClass>]
type LinearTest () =

    [<TestMethod>]
    member this.EmptyEquationHasNoSolution () =
        Assert.AreEqual(None, Linear.solve { Coefficients = []; Constants = [] })

    [<TestMethod>]
    member this.SimpleEqualityHasEmptySolution () =
        Assert.AreEqual(Some Map.empty, Linear.solve { Coefficients = [1]; Constants = [0] })

    [<TestMethod>]
    member this.ConstantMatchOne () =
        let subst =
            Map.empty<int, Linear.Equation>
                .Add(0, { Coefficients = [0; 0; 0; 0; 0; 0; 0; -41]; Constants = [-16] })
                .Add(1, { Coefficients = [0; 0; 0; 0; 0; 0; 0; -64]; Constants = [-25] })
        Assert.AreEqual(Some subst, Linear.solve { Coefficients = [64; -41]; Constants = [1] })