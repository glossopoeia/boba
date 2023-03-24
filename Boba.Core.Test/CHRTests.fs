module CHRTests

open Xunit
open Boba.Core.Fresh
open Boba.Core.DotSeq
open Boba.Core.Kinds
open Boba.Core.Types
open Boba.Core.TypeBuilder
open Boba.Core.Unification
open Boba.Core.CHR

let intType = typeCon "Int" primValueKind
let floatType = typeCon "Float" primValueKind
let boolType = typeCon "Bool" primValueKind
let listType = typeApp (typeCon "[]" (karrow primValueKind primValueKind))
let fnType arg ret = typeApp (typeApp (typeCon "->" (karrow primValueKind (karrow primValueKind primValueKind))) arg) ret

let leqInsRules = [
    // Leq (Int -> Int -> Bool) <==> True
    RSimplification ([typeConstraint "Leq" [fnType intType (fnType intType boolType)]], SEnd)
    // Leq (Float -> Float -> Bool) <==> True
    RSimplification ([typeConstraint "Leq" [fnType floatType (fnType floatType boolType)]], SEnd)
    // Ins ([a] -> a -> [a]) <==> Leq (a -> a -> Bool)
    RSimplification (
        [typeConstraint "Ins" [fnType (listType (valueVar "a")) (fnType (valueVar "a") (listType (valueVar "a")))]],
        (ind (CPredicate (typeConstraint "Leq" [fnType (valueVar "a") (fnType (valueVar "a") boolType)])) SEnd))
    // Leq t ==> t = a -> a -> Bool
    RPropagation ([typeConstraint "Leq" [valueVar "t"]], [CEquality (typeEqConstraint (valueVar "t") (fnType (valueVar "a") (fnType (valueVar "a") boolType)))])
    // Ins t ==> t = ce -> e -> ce
    RPropagation ([typeConstraint "Ins" [valueVar "t"]], [CEquality (typeEqConstraint (valueVar "t") (fnType (valueVar "ce") (fnType (valueVar "c") (valueVar "ce"))))])
    // Ins ([a] -> b -> [a]) ==> b = a
    RPropagation (
        [typeConstraint "Ins" [fnType (listType (valueVar "a")) (fnType (valueVar "b") (listType (valueVar "a")))]],
        [CEquality (typeEqConstraint (valueVar "b") (valueVar "a"))])
]

let ordEqRules = [
    // Eq (Int -> Int -> Bool) <==> True
    RSimplification ([typeConstraint "Eq" [fnType intType (fnType intType boolType)]], SEnd)
    // Eq ([a] -> [a] -> Bool) <==> Eq (a -> a -> Bool)
    RSimplification (
        [typeConstraint "Eq" [fnType (listType (valueVar "a")) (fnType (listType (valueVar "a")) boolType)]],
        (ind (CPredicate (typeConstraint "Eq" [fnType (valueVar "a") (fnType (valueVar "a") boolType)])) SEnd))
    // Ord ([a] -> [a] -> Bool) <==> True
    RSimplification ([typeConstraint "Ord" [fnType (listType (valueVar "a")) (fnType (listType (valueVar "a")) boolType)]], SEnd)
    // Ord t ==> Eq t
    RPropagation ([typeConstraint "Ord" [valueVar "t"]], [CPredicate (typeConstraint "Eq" [valueVar "t"])])
]

let eqLeqSimplRules = [
    // Eq t, Leq t <==> Ord t
    RSimplification (
        [typeConstraint "Eq" [valueVar "t"]; typeConstraint "Leq" [valueVar "t"]],
        ind (CPredicate (typeConstraint "Ord" [valueVar "t"])) SEnd)
]

[<Fact>]
let ``Compute 'Ins ([z] -> y -> x)' ~> 'Leq (z -> z -> Bool)'`` () =
    let problem = Set.singleton (typeConstraint "Ins" [fnType (listType (valueVar "z")) (fnType (valueVar "y") (valueVar "x"))])
    let result = typeConstraint "Leq" [fnType (valueVar "z") (fnType (valueVar "z") boolType)]
    let fresh = new SimpleFresh(0)
    let res = solvePredicates fresh true leqInsRules problem
    Assert.StrictEqual(1, res.Length)
    Assert.True(isTypeMatch fresh result (fst res[0]).MaximumElement)
    Assert.True(isTypeMatch fresh (fst res[0]).MaximumElement result)

[<Fact>]
let ``Compute 'Ord ([a] -> [a] -> Bool)' ~> '' and 'Eq (a -> a -> Bool)'`` () =
    let problem = Set.singleton (typeConstraint "Ord" [fnType (listType (valueVar "a")) (fnType (listType (valueVar "a")) boolType)])
    let resultTwo = typeConstraint "Eq" [fnType (valueVar "a") (fnType (valueVar "a") boolType)]
    let fresh = new SimpleFresh(0)
    let res = solvePredicates fresh true ordEqRules problem
    Assert.StrictEqual(2, res.Length)
    Assert.StrictEqual(Set.empty, fst res[1])
    Assert.True(isTypeMatch fresh resultTwo (fst res[0]).MaximumElement)
    Assert.True(isTypeMatch fresh (fst res[0]).MaximumElement resultTwo)

[<Fact>]
let ``Multihead simplification 'Eq t, Leq t' ~> 'Ord t'`` () =
    let problem =
        Set.empty
        |> Set.add (typeConstraint "Leq" [valueVar "a"])
        |> Set.add (typeConstraint "Eq" [valueVar "a"])
    let result = typeConstraint "Ord" [valueVar "a"]
    let fresh = new SimpleFresh(0)
    let res = solvePredicates fresh true eqLeqSimplRules problem
    Assert.StrictEqual(1, res.Length)
    Assert.StrictEqual(1, Set.count (fst res[0]))
    Assert.True(isTypeMatch fresh result (fst res[0]).MaximumElement)
    Assert.True(isTypeMatch fresh (fst res[0]).MaximumElement result)

[<Fact>]
let ``Multihead simplification that doesnt reduce`` () =
    let problem =
        Set.empty
        |> Set.add (typeConstraint "Leq" [valueVar "a"])
        |> Set.add (typeConstraint "Eq" [valueVar "b"])
    let fresh = new SimpleFresh(0)
    let res = solvePredicates fresh true eqLeqSimplRules problem
    Assert.StrictEqual(1, res.Length)
    Assert.StrictEqual(2, Set.count (fst res[0]))