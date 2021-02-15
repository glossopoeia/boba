module LinearTests

open Xunit
open Boba.Core
open FsCheck
open FsCheck.Xunit

[<Fact>]
let ``Empty equation has no solution`` () =
    Assert.StrictEqual(None, Linear.solve { Coefficients = []; Constants = [] })

[<Property>]
let ``Simple equality has just its equality as solution`` (NonZeroInt coeff) =
    let subst = Map.empty<int, Linear.Equation>.Add(0, { Coefficients = [0]; Constants = [0] })
    Assert.StrictEqual(Some subst, Linear.solve { Coefficients = [coeff]; Constants = [0] })

[<Property>]
let ``Two variables with the same coefficients is equivalent to subtraction`` (NonZeroInt coeff) =
    let subst = Map.empty<int, Linear.Equation>.Add(0, { Coefficients = [0; -1]; Constants = [0] })
    Assert.StrictEqual(Some subst, Linear.solve { Coefficients = [coeff; coeff]; Constants = [0] })

[<Property>]
let ``Two variables with inverted coefficients is equivalent to addition`` (NonZeroInt coeff) =
    let subst = Map.empty<int, Linear.Equation>.Add(0, { Coefficients = [0; 1]; Constants = [0] })
    Assert.StrictEqual(Some subst, Linear.solve { Coefficients = [coeff; -coeff]; Constants = [0] })

[<Property>]
let ``Two variables with inverted coefficients equal to double the absoute value of their coefficients`` (NonZeroInt coeff) =
    let subst = Map.empty<int, Linear.Equation>.Add(0, { Coefficients = [0; 1]; Constants = [2] })
    Assert.StrictEqual(Some subst, Linear.solve { Coefficients = [coeff; -coeff]; Constants = [coeff * 2] })

[<Fact>]
let ``5x + 10y = 18  ~~> no solution`` () =
    Assert.StrictEqual(None, Linear.solve { Coefficients = [5; 10]; Constants = [18] })

[<Fact>]
let ``Complex matching two variable test #1: 5x + 3y = 0`` () =
    let subst =
        Map.empty<int, Linear.Equation>
            .Add(0, { Coefficients = [0; 0; 0; 3]; Constants = [0] })
            .Add(1, { Coefficients = [0; 0; 0; -5]; Constants = [0] })
    Assert.StrictEqual(Some subst, Linear.solve { Coefficients = [5; 3]; Constants = [0] })

[<Fact>]
let ``Complex matching two variable test #2: 64x - 41y = 1`` () =
    let subst =
        Map.empty<int, Linear.Equation>
            .Add(0, { Coefficients = [0; 0; 0; 0; 0; 0; -41]; Constants = [-16] })
            .Add(1, { Coefficients = [0; 0; 0; 0; 0; 0; -64]; Constants = [-25] })
    Assert.StrictEqual(Some subst, Linear.solve { Coefficients = [64; -41]; Constants = [1] })