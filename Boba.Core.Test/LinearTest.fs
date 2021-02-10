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
        let subst = Map.empty<int, Linear.Equation>.Add(0, { Coefficients = [0]; Constants = [0] })
        Assert.AreEqual(Some subst, Linear.solve { Coefficients = [1]; Constants = [0] })

    [<TestMethod>]
    member this.TwoVariablesWithSameConstantsEqualZeroIsSubtraction () =
        let subst = Map.empty<int, Linear.Equation>.Add(0, { Coefficients = [0; -1]; Constants = [0] })
        Assert.AreEqual(Some subst, Linear.solve { Coefficients = [5; 5]; Constants = [0] })

    [<TestMethod>]
    member this.TwoVariablesWithInvertedConstantsEqualZeroIsAddition () =
        let subst = Map.empty<int, Linear.Equation>.Add(0, { Coefficients = [0; 1]; Constants = [0] })
        Assert.AreEqual(Some subst, Linear.solve { Coefficients = [5; -5]; Constants = [0] })

    [<TestMethod>]
    member this.TwoVariablesWithInvertedConstantsEqualTwiceAbsOfBoth () =
        let subst = Map.empty<int, Linear.Equation>.Add(0, { Coefficients = [0; 1]; Constants = [2] })
        Assert.AreEqual(Some subst, Linear.solve { Coefficients = [5; -5]; Constants = [10] })

    [<TestMethod>]
    member this.NoSolutionOne () =
        Assert.AreEqual(None, Linear.solve { Coefficients = [5; 10]; Constants = [18] })

    [<TestMethod>]
    member this.ComplexMatchTwoVariablesOne () =
        let subst =
            Map.empty<int, Linear.Equation>
                .Add(0, { Coefficients = [0; 0; 0; 3]; Constants = [0] })
                .Add(1, { Coefficients = [0; 0; 0; -5]; Constants = [0] })
        Assert.AreEqual(Some subst, Linear.solve { Coefficients = [5; 3]; Constants = [0] })

    [<TestMethod>]
    member this.ComplexMatchTwoVariablesTwo () =
        let subst =
            Map.empty<int, Linear.Equation>
                .Add(0, { Coefficients = [0; 0; 0; 0; 0; 0; -41]; Constants = [-16] })
                .Add(1, { Coefficients = [0; 0; 0; 0; 0; 0; -64]; Constants = [-25] })
        Assert.AreEqual(Some subst, Linear.solve { Coefficients = [64; -41]; Constants = [1] })