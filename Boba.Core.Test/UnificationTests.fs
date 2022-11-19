module UnificationTests

open Xunit
open Boba.Core.DotSeq
open Boba.Core.Fresh
open Boba.Core.Kinds
open Boba.Core.Types
open Boba.Core.Unification

[<Fact>]
let ``Unify succeed: A ~ A`` () =
    let tsub, ksub = typeUnifyExn (new SimpleFresh(0)) (typeCon "A" primValueKind) (typeCon "A" primValueKind)
    Assert.StrictEqual(Map.empty, tsub)
    Assert.StrictEqual(Map.empty, ksub)

[<Fact>]
let ``Unify fail: A ~ B -- constructor mismatch`` () =
    Assert.Throws<UnifyRigidRigidMismatch>(fun () -> typeUnifyExn (new SimpleFresh(0)) (typeCon "A" primValueKind) (typeCon "B" primValueKind) |> ignore)

[<Fact>]
let ``Unify succeed: a ~ a`` () =
    let tsub, ksub = typeUnifyExn (new SimpleFresh(0)) (typeVar "a" primValueKind) (typeVar "a" primValueKind)
    Assert.StrictEqual(Map.empty, tsub)
    Assert.StrictEqual(Map.empty, ksub)

[<Fact>]
let ``Unify succeed: a ~ b`` () =
    let tsub, ksub = typeUnifyExn (new SimpleFresh(0)) (typeVar "a" primValueKind) (typeVar "b" primValueKind)
    Assert.StrictEqual(Map.empty.Add("a", (typeVar "b" primValueKind)), tsub)
    Assert.StrictEqual(Map.empty, ksub)

[<Fact>]
let ``Unify fail: a ~ (b a) -- occurs check`` () =
    Assert.Throws<UnifyTypeOccursCheckFailure>(fun () -> typeUnifyExn (new SimpleFresh(0)) (typeVar "a" primValueKind) (typeApp (typeVar "b" (karrow primValueKind primValueKind)) (typeVar "a" primValueKind)) |> ignore)

[<Fact>]
let ``Unify succeed: a ~ (B c)`` () =
    let tsub, ksub = typeUnifyExn (new SimpleFresh(0)) (typeVar "a" primValueKind) (typeApp (typeCon "B" (karrow primValueKind primValueKind)) (typeVar "c" primValueKind))
    Assert.StrictEqual(
        Map.empty.Add("a", (typeApp (typeCon "B" (karrow primValueKind primValueKind)) (typeVar "c" primValueKind))),
        tsub)
    Assert.StrictEqual(Map.empty, ksub)

[<Fact>]
let ``Unify succeed: (a B) ~ (c d)`` () =
    let tsub, ksub = typeUnifyExn (new SimpleFresh(0)) (typeApp (typeVar "a" (karrow primValueKind primValueKind)) (typeCon "B" primValueKind)) (typeApp (typeVar "c" (karrow primValueKind primValueKind)) (typeVar "d" primValueKind))
    Assert.StrictEqual(
        Map.empty.Add("a", typeVar "c" (karrow primValueKind primValueKind)).Add("d", typeCon "B" primValueKind),
        tsub)
    Assert.StrictEqual(Map.empty, ksub)



[<Fact>]
let ``Unify succeed: b B a ... ~ c c e d ...`` () =
    let tsub, ksub =
        typeUnifyExn (new SimpleFresh(0))
            (typeValueSeq (SInd (typeVar "b" primValueKind, SInd (typeCon "B" primValueKind, SDot (typeVar "a" primValueKind, SEnd)))))
            (typeValueSeq (SInd (typeVar "c" primValueKind, SInd (typeVar "c" primValueKind, SInd (typeVar "e" primValueKind, SDot (typeVar "d" primValueKind, SEnd))))))
    Assert.StrictEqual(
        Map.empty
            .Add("b", typeCon "B" primValueKind)
            .Add("c", typeCon "B" primValueKind)
            .Add("a", typeValueSeq (SInd (typeVar "e" primValueKind, SDot (typeVar "d" primValueKind, SEnd))))
            .Add("a0", typeVar "e" primValueKind)
            .Add("a1", typeVar "d" primValueKind),
        tsub)
    Assert.StrictEqual(Map.empty, ksub)

[<Fact>]
let ``Unify succeed: (V a b) ~ (V c d)...`` () =
    let vcon = typeCon "V" (karrow primDataKind (karrow primSharingKind primValueKind))
    let tsub, ksub =
        typeUnifyExn (new SimpleFresh(0))
            (typeValueSeq (ind (typeApp (typeApp vcon (typeVar "a" primDataKind)) (typeVar "b" primSharingKind)) SEnd))
            (typeValueSeq (dot (typeApp (typeApp vcon (typeVar "c" primDataKind)) (typeVar "d" primSharingKind)) SEnd))
    Assert.StrictEqual(
        Map.empty
            .Add("c", typeSeq (ind (typeVar "a" primDataKind) SEnd) primDataKind)
            .Add("d", typeSeq (ind (typeVar "b" primSharingKind) SEnd) primSharingKind)
            .Add("c0", typeVar "a" primDataKind)
            .Add("c1", typeSeq SEnd primDataKind)
            .Add("d2", typeVar "b" primSharingKind)
            .Add("d3", typeSeq SEnd primSharingKind),
        tsub)
    Assert.StrictEqual(Map.empty, ksub)

[<Fact>]
let ``Unify fail: a ... ~ b a...`` () =
    Assert.Throws<UnifyTypeOccursCheckFailure>(fun () ->
        typeUnifyExn (new SimpleFresh(0)) (typeValueSeq (SDot (typeVar "a" primValueKind, SEnd))) (typeValueSeq (SInd (typeVar "b" primValueKind, SDot (typeVar "a" primValueKind, SEnd)))) |> ignore)

[<Fact>]
let ``Unify fail: one: a, b... ~ two: c, b...`` () =
    Assert.Throws<UnifyRowRigidMismatch>(fun () ->
        typeUnifyExn (new SimpleFresh(0))
            (typeApp (typeApp (TRowExtend primFieldKind) (typeApp (typeCon "one" (karrow primValueKind primFieldKind)) (typeVar "a" primValueKind))) (typeVar "b" (KRow primFieldKind)))
            (typeApp (typeApp (TRowExtend primFieldKind) (typeApp (typeCon "two" (karrow primValueKind primFieldKind)) (typeVar "c" primValueKind))) (typeVar "b" (KRow primFieldKind))) |> ignore)