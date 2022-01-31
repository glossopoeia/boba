module CHRTests

open Xunit
open Boba.Core.Fresh
open Boba.Core.Kinds
open Boba.Core.Types
open Boba.Core.TypeBuilder
open Boba.Core.Unification
open Boba.Core.CHR

let intType = typeCon "Int" KValue
let floatType = typeCon "Float" KValue
let boolType = typeCon "Bool" KValue
let listType = typeApp (typeCon "[]" (karrow KValue KValue))
let fnType arg ret = typeApp (typeApp (typeCon "->" (karrow KValue (karrow KValue KValue))) arg) ret

let leqInsRules = [
    // Leq (Int -> Int -> Bool) <==> True
    RSimplification ([typeConstraint "Leq" (fnType intType (fnType intType boolType))], [])
    // Leq (Float -> Float -> Bool) <==> True
    RSimplification ([typeConstraint "Leq" (fnType floatType (fnType floatType boolType))], [])
    // Ins ([a] -> a -> [a]) <==> Leq (a -> a -> Bool)
    RSimplification (
        [typeConstraint "Ins" (fnType (listType (valueVar "a")) (fnType (valueVar "a") (listType (valueVar "a"))))],
        [CPredicate (typeConstraint "Leq" (fnType (valueVar "a") (fnType (valueVar "a") boolType)))])
    // Leq t ==> t = a -> a -> Bool
    RPropagation ([typeConstraint "Leq" (valueVar "t")], [CEquality { Left = valueVar "t"; Right = fnType (valueVar "a") (fnType (valueVar "a") boolType) }])
    // Ins t ==> t = ce -> e -> ce
    RPropagation ([typeConstraint "Ins" (valueVar "t")], [CEquality { Left = valueVar "t"; Right = fnType (valueVar "ce") (fnType (valueVar "c") (valueVar "ce")) }])
    // Ins ([a] -> b -> [a]) ==> b = a
    RPropagation (
        [typeConstraint "Ins" (fnType (listType (valueVar "a")) (fnType (valueVar "b") (listType (valueVar "a"))))],
        [CEquality { Left = valueVar "b"; Right = valueVar "a" }])
]

[<Fact>]
let ``Compute 'Ins ([z] -> y -> x)' ~> 'Leq (z -> z -> Bool)'`` () =
    let problem = Set.singleton (typeConstraint "Ins" (fnType (listType (valueVar "z")) (fnType (valueVar "y") (valueVar "x"))))
    let fresh = new SimpleFresh(0)
    let res = solvePredicates fresh leqInsRules problem
    printfn $"Results: !!!"
    Seq.iter (fun r -> printfn $"    {r}") res
    printfn $"res: {fst res[0]}"
    printfn $"subst: {snd res[0]}"
    Assert.StrictEqual(1, res.Length)