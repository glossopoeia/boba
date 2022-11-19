module KindTests

open Xunit
open Boba.Core.Kinds

[<Fact>]
let ``No top kind equality`` () =
    Assert.True(
        kindEq
            (karrow (kseq (krow (kvar "s"))) (krow (kseq (KUser ("K", KUSyntactic)))))
            (karrow (kseq (krow (kvar "s"))) (krow (kseq (KUser ("K", KUSyntactic))))))

[<Fact>]
let ``Top kind equality`` () =
    Assert.True(kindEq KAny (kvar "s"))
    Assert.True(kindEq (kvar "s") KAny)
    Assert.True(
        kindEq
            (karrow (kseq (krow KAny)) (krow (kseq (KUser ("K", KUSyntactic)))))
            (karrow (kseq (krow (kvar "s"))) (krow (kseq KAny))))

[<Fact>]
let ``Can apply kind respects _ supertype in arrow`` () =
    Assert.True(canApplyKind (karrow (kvar "i") (kvar "o")) (kvar "i"))
    Assert.True(canApplyKind (karrow KAny (kvar "o")) (kvar "i"))
    Assert.True(canApplyKind (karrow (kseq KAny) (kvar "o")) (kseq (kvar "i")))

[<Fact>]
let ``Can apply kind respects _ supertype in argument`` () =
    Assert.True(canApplyKind (karrow (krow (kvar "i")) (kvar "o")) (krow (kvar "i")))
    Assert.True(canApplyKind (karrow (kvar "i") (kvar "o")) KAny)
    Assert.True(canApplyKind (karrow (kseq (kvar "i")) (kvar "o")) (kseq KAny))
    Assert.True(canApplyKind (karrow (kseq (kseq (kvar "s"))) (kvar "o")) (kseq KAny))

[<Fact>]
let ``Can apply fails when not arrow and arg not equal input`` () =
    Assert.False(canApplyKind (kvar "s") (kvar "s"))
    Assert.False(canApplyKind (kseq (kvar "s")) KAny)
    Assert.False(canApplyKind KAny KAny)
    Assert.False(canApplyKind (karrow (kvar "i") (kvar "o")) (kvar "x"))
    Assert.False(canApplyKind (karrow (kseq (kseq (kvar "s"))) (kvar "o")) (kseq (kvar "s")))

[<Fact>]
let ``Kind apply respects _ supertype in arrow`` () =
    Assert.StrictEqual(kvar "o", applyKindExn (karrow (kvar "i") (kvar "o")) (kvar "i"))
    Assert.StrictEqual(kvar "o", applyKindExn (karrow KAny (kvar "o")) (kvar "i"))
    Assert.StrictEqual(kvar "o", applyKindExn (karrow (kseq KAny) (kvar "o")) (kseq (kvar "i")))

[<Fact>]
let ``Kind apply respects _ supertype in argument`` () =
    Assert.StrictEqual(kvar "o", applyKindExn (karrow (krow (kvar "i")) (kvar "o")) (krow (kvar "i")))
    Assert.StrictEqual(kvar "o", applyKindExn (karrow (kvar "i") (kvar "o")) KAny)
    Assert.StrictEqual(kvar "o", applyKindExn (karrow (kseq (kvar "i")) (kvar "o")) (kseq KAny))

[<Fact>]
let ``Kind apply throws when not arrow and arg not equal input`` () =
    Assert.Throws<KindApplyNotArrow>(fun () -> applyKindExn (kvar "s") (kvar "s") |> ignore)
    Assert.Throws<KindApplyNotArrow>(fun () -> applyKindExn (kseq (kvar "s")) KAny |> ignore)
    Assert.Throws<KindApplyNotArrow>(fun () -> applyKindExn KAny KAny |> ignore)
    Assert.Throws<KindApplyArgMismatch>(fun () -> applyKindExn (karrow (kvar "i") (kvar "o")) (kvar "x") |> ignore)