module UnificationTests

open Xunit
open Boba.Core.DotSeq
open Boba.Core.Fresh
open Boba.Core.Kinds
open Boba.Core.Types
open Boba.Core.Unification

[<Fact>]
let ``Unify succeed: A ~ A`` () =
    Assert.StrictEqual(Map.empty, typeUnifyExn (new SimpleFresh(0)) (typeCon "A" KValue) (typeCon "A" KValue))

[<Fact>]
let ``Unify fail: A ~ B -- constructor mismatch`` () =
    Assert.Throws<UnifyRigidRigidMismatch>(fun () -> typeUnifyExn (new SimpleFresh(0)) (typeCon "A" KValue) (typeCon "B" KValue) |> ignore)

[<Fact>]
let ``Unify succeed: a ~ a`` () =
    Assert.StrictEqual(Map.empty, typeUnifyExn (new SimpleFresh(0)) (typeVar "a" KValue) (typeVar "a" KValue))

[<Fact>]
let ``Unify succeed: a ~ b`` () =
    Assert.StrictEqual(Map.empty.Add("a", (typeVar "b" KValue)), typeUnifyExn (new SimpleFresh(0)) (typeVar "a" KValue) (typeVar "b" KValue))

[<Fact>]
let ``Unify fail: a ~ (b a) -- occurs check`` () =
    Assert.Throws<UnifyOccursCheckFailure>(fun () -> typeUnifyExn (new SimpleFresh(0)) (typeVar "a" KValue) (typeApp (typeVar "b" (karrow KValue KValue)) (typeVar "a" KValue)) |> ignore)

[<Fact>]
let ``Unify succeed: a ~ (B c)`` () =
    Assert.StrictEqual(
        Map.empty.Add("a", (typeApp (typeCon "B" (karrow KValue KValue)) (typeVar "c" KValue))),
        typeUnifyExn (new SimpleFresh(0)) (typeVar "a" KValue) (typeApp (typeCon "B" (karrow KValue KValue)) (typeVar "c" KValue)))

[<Fact>]
let ``Unify succeed: (a B) ~ (c d)`` () =
    Assert.StrictEqual(
        Map.empty.Add("a", typeVar "c" (karrow KValue KValue)).Add("d", typeCon "B" KValue),
        typeUnifyExn (new SimpleFresh(0)) (typeApp (typeVar "a" (karrow KValue KValue)) (typeCon "B" KValue)) (typeApp (typeVar "c" (karrow KValue KValue)) (typeVar "d" KValue)))



[<Fact>]
let ``Unify succeed: b B a ... ~ c c e d ...`` () =
    Assert.StrictEqual(
        Map.empty
            .Add("b", typeCon "B" KValue)
            .Add("c", typeCon "B" KValue)
            .Add("a", TSeq (SInd (typeVar "e" KValue, SDot (typeVar "d" KValue, SEnd)), KValue))
            .Add("a0", typeVar "e" KValue)
            .Add("a1", typeVar "d" KValue),
        typeUnifyExn (new SimpleFresh(0))
            (TSeq (SInd (typeVar "b" KValue, SInd (typeCon "B" KValue, SDot (typeVar "a" KValue, SEnd))), KValue))
            (TSeq (SInd (typeVar "c" KValue, SInd (typeVar "c" KValue, SInd (typeVar "e" KValue, SDot (typeVar "d" KValue, SEnd)))), KValue)))

[<Fact>]
let ``Unify fail: a ... ~ b a...`` () =
    Assert.Throws<UnifyOccursCheckFailure>(fun () ->
        typeUnifyExn (new SimpleFresh(0)) (TSeq (SDot (typeVar "a" KValue, SEnd), KValue)) (TSeq (SInd (typeVar "b" KValue, SDot (typeVar "a" KValue, SEnd)), KValue)) |> ignore)

[<Fact>]
let ``Unify fail: one: a, b... ~ two: c, b...`` () =
    Assert.Throws<UnifyRowRigidMismatch>(fun () ->
        typeUnifyExn (new SimpleFresh(0))
            (typeApp (typeApp (TRowExtend KField) (typeApp (typeCon "one" (karrow KValue KField)) (typeVar "a" KValue))) (typeVar "b" (KRow KField)))
            (typeApp (typeApp (TRowExtend KField) (typeApp (typeCon "two" (karrow KValue KField)) (typeVar "c" KValue))) (typeVar "b" (KRow KField))) |> ignore)