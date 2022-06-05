module UnificationTests

open Xunit
open Boba.Core.DotSeq
open Boba.Core.Fresh
open Boba.Core.Kinds
open Boba.Core.Types
open Boba.Core.Unification

[<Fact>]
let ``Unify succeed: A ~ A`` () =
    Assert.StrictEqual(Map.empty, typeUnifyExn (new SimpleFresh(0)) (typeCon "A" primValueKind) (typeCon "A" primValueKind))

[<Fact>]
let ``Unify fail: A ~ B -- constructor mismatch`` () =
    Assert.Throws<UnifyRigidRigidMismatch>(fun () -> typeUnifyExn (new SimpleFresh(0)) (typeCon "A" primValueKind) (typeCon "B" primValueKind) |> ignore)

[<Fact>]
let ``Unify succeed: a ~ a`` () =
    Assert.StrictEqual(Map.empty, typeUnifyExn (new SimpleFresh(0)) (typeVar "a" primValueKind) (typeVar "a" primValueKind))

[<Fact>]
let ``Unify succeed: a ~ b`` () =
    Assert.StrictEqual(Map.empty.Add("a", (typeVar "b" primValueKind)), typeUnifyExn (new SimpleFresh(0)) (typeVar "a" primValueKind) (typeVar "b" primValueKind))

[<Fact>]
let ``Unify fail: a ~ (b a) -- occurs check`` () =
    Assert.Throws<UnifyOccursCheckFailure>(fun () -> typeUnifyExn (new SimpleFresh(0)) (typeVar "a" primValueKind) (typeApp (typeVar "b" (karrow primValueKind primValueKind)) (typeVar "a" primValueKind)) |> ignore)

[<Fact>]
let ``Unify succeed: a ~ (B c)`` () =
    Assert.StrictEqual(
        Map.empty.Add("a", (typeApp (typeCon "B" (karrow primValueKind primValueKind)) (typeVar "c" primValueKind))),
        typeUnifyExn (new SimpleFresh(0)) (typeVar "a" primValueKind) (typeApp (typeCon "B" (karrow primValueKind primValueKind)) (typeVar "c" primValueKind)))

[<Fact>]
let ``Unify succeed: (a B) ~ (c d)`` () =
    Assert.StrictEqual(
        Map.empty.Add("a", typeVar "c" (karrow primValueKind primValueKind)).Add("d", typeCon "B" primValueKind),
        typeUnifyExn (new SimpleFresh(0)) (typeApp (typeVar "a" (karrow primValueKind primValueKind)) (typeCon "B" primValueKind)) (typeApp (typeVar "c" (karrow primValueKind primValueKind)) (typeVar "d" primValueKind)))



[<Fact>]
let ``Unify succeed: b B a ... ~ c c e d ...`` () =
    Assert.StrictEqual(
        Map.empty
            .Add("b", typeCon "B" primValueKind)
            .Add("c", typeCon "B" primValueKind)
            .Add("a", TSeq (SInd (typeVar "e" primValueKind, SDot (typeVar "d" primValueKind, SEnd)), primValueKind))
            .Add("a0", typeVar "e" primValueKind)
            .Add("a1", typeVar "d" primValueKind),
        typeUnifyExn (new SimpleFresh(0))
            (TSeq (SInd (typeVar "b" primValueKind, SInd (typeCon "B" primValueKind, SDot (typeVar "a" primValueKind, SEnd))), primValueKind))
            (TSeq (SInd (typeVar "c" primValueKind, SInd (typeVar "c" primValueKind, SInd (typeVar "e" primValueKind, SDot (typeVar "d" primValueKind, SEnd)))), primValueKind)))

[<Fact>]
let ``Unify fail: a ... ~ b a...`` () =
    Assert.Throws<UnifyOccursCheckFailure>(fun () ->
        typeUnifyExn (new SimpleFresh(0)) (TSeq (SDot (typeVar "a" primValueKind, SEnd), primValueKind)) (TSeq (SInd (typeVar "b" primValueKind, SDot (typeVar "a" primValueKind, SEnd)), primValueKind)) |> ignore)

[<Fact>]
let ``Unify fail: one: a, b... ~ two: c, b...`` () =
    Assert.Throws<UnifyRowRigidMismatch>(fun () ->
        typeUnifyExn (new SimpleFresh(0))
            (typeApp (typeApp (TRowExtend primFieldKind) (typeApp (typeCon "one" (karrow primValueKind primFieldKind)) (typeVar "a" primValueKind))) (typeVar "b" (KRow primFieldKind)))
            (typeApp (typeApp (TRowExtend primFieldKind) (typeApp (typeCon "two" (karrow primValueKind primFieldKind)) (typeVar "c" primValueKind))) (typeVar "b" (KRow primFieldKind))) |> ignore)