module UnificationTests

open Xunit
open Boba.Core.DotSeq
open Boba.Core.Fresh
open Boba.Core.Kinds
open Boba.Core.Types
open Boba.Core.Unification

[<Fact>]
let ``Unify succeed: A ~ A`` () =
    let subst = typeUnifyExn (new SimpleFresh(0)) (typeCon "A" primValueKind) (typeCon "A" primValueKind)
    Assert.StrictEqual(Map.empty, subst.Types)
    Assert.StrictEqual(Map.empty, subst.Types)

[<Fact>]
let ``Unify fail: A ~ B -- constructor mismatch`` () =
    Assert.Throws<UnifyRigidRigidMismatch>(fun () -> typeUnifyExn (new SimpleFresh(0)) (typeCon "A" primValueKind) (typeCon "B" primValueKind) |> ignore)

[<Fact>]
let ``Unify succeed: a ~ a`` () =
    let subst = typeUnifyExn (new SimpleFresh(0)) (typeVar "a" primValueKind) (typeVar "a" primValueKind)
    Assert.StrictEqual(Map.empty, subst.Types)
    Assert.StrictEqual(Map.empty, subst.Kinds)

[<Fact>]
let ``Unify succeed: a ~ b`` () =
    let subst = typeUnifyExn (new SimpleFresh(0)) (typeVar "a" primValueKind) (typeVar "b" primValueKind)
    Assert.StrictEqual(Map.empty.Add("a", (typeVar "b" primValueKind)), subst.Types)
    Assert.StrictEqual(Map.empty, subst.Kinds)

[<Fact>]
let ``Unify fail: a ~ (b a) -- occurs check`` () =
    Assert.Throws<UnifyTypeOccursCheckFailure>(fun () -> typeUnifyExn (new SimpleFresh(0)) (typeVar "a" primValueKind) (typeApp (typeVar "b" (karrow primValueKind primValueKind)) (typeVar "a" primValueKind)) |> ignore)

[<Fact>]
let ``Unify succeed: a ~ (B c)`` () =
    let subst = typeUnifyExn (new SimpleFresh(0)) (typeVar "a" primValueKind) (typeApp (typeCon "B" (karrow primValueKind primValueKind)) (typeVar "c" primValueKind))
    Assert.StrictEqual(
        Map.empty.Add("a", (typeApp (typeCon "B" (karrow primValueKind primValueKind)) (typeVar "c" primValueKind))),
        subst.Types)
    Assert.StrictEqual(Map.empty, subst.Kinds)

[<Fact>]
let ``Unify succeed: (a B) ~ (c d)`` () =
    let subst = typeUnifyExn (new SimpleFresh(0)) (typeApp (typeVar "a" (karrow primValueKind primValueKind)) (typeCon "B" primValueKind)) (typeApp (typeVar "c" (karrow primValueKind primValueKind)) (typeVar "d" primValueKind))
    Assert.StrictEqual(
        Map.empty.Add("a", typeVar "c" (karrow primValueKind primValueKind)).Add("d", typeCon "B" primValueKind),
        subst.Types)
    Assert.StrictEqual(Map.empty, subst.Kinds)



[<Fact>]
let ``Unify succeed: b B a ... ~ c c e d ...`` () =
    let subst =
        typeUnifyExn (new SimpleFresh(0))
            (typeSeq (SInd (typeVar "b" primValueKind, SInd (typeCon "B" primValueKind, SDot (typeVar "a" primValueKind, SEnd)))))
            (typeSeq (SInd (typeVar "c" primValueKind, SInd (typeVar "c" primValueKind, SInd (typeVar "e" primValueKind, SDot (typeVar "d" primValueKind, SEnd))))))
    Assert.StrictEqual(
        Map.empty
            .Add("b", typeCon "B" primValueKind)
            .Add("c", typeCon "B" primValueKind)
            .Add("a", typeSeq (SInd (typeVar "e" primValueKind, SDot (typeVar "d" primValueKind, SEnd))))
            .Add("a0", typeVar "e" primValueKind)
            .Add("a1", typeVar "d" primValueKind),
        subst.Types)
    Assert.StrictEqual(Map.empty, subst.Kinds)

[<Fact>]
let ``Unify succeed: (V a b) ~ (V c d)...`` () =
    let vcon = typeCon "V" (karrow primDataKind (karrow primSharingKind primValueKind))
    let subst =
        typeUnifyExn (new SimpleFresh(0))
            (typeSeq (ind (typeApp (typeApp vcon (typeVar "a" primDataKind)) (typeVar "b" primSharingKind)) SEnd))
            (typeSeq (dot (typeApp (typeApp vcon (typeVar "c" primDataKind)) (typeVar "d" primSharingKind)) SEnd))
    Assert.StrictEqual(
        Map.empty
            .Add("c", typeSeq (ind (typeVar "a" primDataKind) SEnd))
            .Add("d", typeSeq (ind (typeVar "b" primSharingKind) SEnd))
            .Add("c0", typeVar "a" primDataKind)
            .Add("c1", typeSeq SEnd)
            .Add("d2", typeVar "b" primSharingKind)
            .Add("d3", typeSeq SEnd),
        subst.Types)
    Assert.StrictEqual(Map.empty, subst.Kinds)

[<Fact>]
let ``Unify succeed: V<k> ~ a<Data>`` () =
    let subst = typeUnifyExn (new SimpleFresh(0)) (typeCon "V" (kvar "k")) (typeVar "a" primDataKind)
    Assert.StrictEqual(Map.empty.Add("k", primDataKind), subst.Kinds)
    Assert.StrictEqual(Map.empty.Add("a", typeCon "V" primDataKind), subst.Types)

[<Fact>]
let ``Unify succeed: V<k> ~ V<i --> o>`` () =
    let subst = typeUnifyExn (new SimpleFresh(0)) (typeCon "V" (kvar "k")) (typeCon "V" (karrow (kvar "i") (kvar "o")))
    Assert.StrictEqual(Map.empty.Add("k", karrow (kvar "i") (kvar "o")), subst.Kinds)

[<Fact>]
let ``Unify fail: a ... ~ b a...`` () =
    Assert.Throws<UnifyTypeOccursCheckFailure>(fun () ->
        typeUnifyExn (new SimpleFresh(0)) (typeSeq (SDot (typeVar "a" primValueKind, SEnd))) (typeSeq (SInd (typeVar "b" primValueKind, SDot (typeVar "a" primValueKind, SEnd)))) |> ignore)

[<Fact>]
let ``Unify fail: one: a, b... ~ two: c, b...`` () =
    Assert.Throws<UnifyRowRigidMismatch>(fun () ->
        typeUnifyExn (new SimpleFresh(0))
            (typeApp (typeApp (TRowExtend primFieldKind) (typeApp (typeCon "one" (karrow primValueKind primFieldKind)) (typeVar "a" primValueKind))) (typeVar "b" (KRow primFieldKind)))
            (typeApp (typeApp (TRowExtend primFieldKind) (typeApp (typeCon "two" (karrow primValueKind primFieldKind)) (typeVar "c" primValueKind))) (typeVar "b" (KRow primFieldKind))) |> ignore)