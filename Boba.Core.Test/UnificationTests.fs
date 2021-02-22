module UnificationTests

open Xunit
open Boba.Core.DotSeq
open Boba.Core.Fresh
open Boba.Core.Kinds
open Boba.Core.Types
open Boba.Core.Unification

[<Fact>]
let ``Unify succeed: A ~ A`` () =
    Assert.StrictEqual(Map.empty, typeUnifyExn (new SimpleFresh(0)) (typeCon "A" KData) (typeCon "A" KData))

[<Fact>]
let ``Unify fail: A ~ B -- constructor mismatch`` () =
    Assert.Throws<UnifyRigidRigidMismatch>(fun () -> typeUnifyExn (new SimpleFresh(0)) (typeCon "A" KData) (typeCon "B" KData) |> ignore)

[<Fact>]
let ``Unify succeed: a ~ a`` () =
    Assert.StrictEqual(Map.empty, typeUnifyExn (new SimpleFresh(0)) (typeVar "a" KData) (typeVar "a" KData))

[<Fact>]
let ``Unify succeed: a ~ b`` () =
    Assert.StrictEqual(Map.empty.Add("a", (typeVar "b" KData)), typeUnifyExn (new SimpleFresh(0)) (typeVar "a" KData) (typeVar "b" KData))

[<Fact>]
let ``Unify fail: a ~ (b a) -- occurs check`` () =
    Assert.Throws<UnifyOccursCheckFailure>(fun () -> typeUnifyExn (new SimpleFresh(0)) (typeVar "a" KData) (typeApp (typeVar "b" (karrow KData KData)) (typeVar "a" KData)) |> ignore)

[<Fact>]
let ``Unify succeed: a ~ (B c)`` () =
    Assert.StrictEqual(
        Map.empty.Add("a", (typeApp (typeCon "B" (karrow KData KData)) (typeVar "c" KData))),
        typeUnifyExn (new SimpleFresh(0)) (typeVar "a" KData) (typeApp (typeCon "B" (karrow KData KData)) (typeVar "c" KData)))

[<Fact>]
let ``Unify succeed: (a B) ~ (c d)`` () =
    Assert.StrictEqual(
        Map.empty.Add("a", typeVar "c" (karrow KData KData)).Add("d", typeCon "B" KData),
        typeUnifyExn (new SimpleFresh(0)) (typeApp (typeVar "a" (karrow KData KData)) (typeCon "B" KData)) (typeApp (typeVar "c" (karrow KData KData)) (typeVar "d" KData)))



[<Fact>]
let ``Unify succeed: b B a ... ~ c c e d ...`` () =
    Assert.StrictEqual(
        Map.empty
            .Add("b", typeCon "B" KData)
            .Add("c", typeCon "B" KData)
            .Add("a", TSeq (SInd (typeVar "e" KData, SDot (typeVar "d" KData, SEnd))))
            .Add("a0", typeVar "e" KData)
            .Add("a1", typeVar "d" KData),
        typeUnifyExn (new SimpleFresh(0))
            (TSeq (SInd (typeVar "b" KData, SInd (typeCon "B" KData, SDot (typeVar "a" KData, SEnd)))))
            (TSeq (SInd (typeVar "c" KData, SInd (typeVar "c" KData, SInd (typeVar "e" KData, SDot (typeVar "d" KData, SEnd)))))))

[<Fact>]
let ``Unify fail: one: a, b... ~ two: c, b...`` () =
    Assert.Throws<UnifyRowRigidMismatch>(fun () ->
        typeUnifyExn (new SimpleFresh(0))
            (typeApp (typeApp (TRowExtend KField) (typeApp (typeCon "one" (karrow KData KField)) (typeVar "a" KData))) (typeVar "b" (KRow KField)))
            (typeApp (typeApp (TRowExtend KField) (typeApp (typeCon "two" (karrow KData KField)) (typeVar "c" KData))) (typeVar "b" (KRow KField))) |> ignore)