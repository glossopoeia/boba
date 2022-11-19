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
let ``Kind apply respects _ supertype in arrow`` () =
    Assert.StrictEqual(kvar "o", applyKindExn (karrow (kvar "i") (kvar "o")) (kvar "i"))
    Assert.StrictEqual(kvar "o", applyKindExn (karrow KAny (kvar "o")) (kvar "i"))
    Assert.StrictEqual(kvar "o", applyKindExn (karrow (kseq KAny) (kvar "o")) (kseq (kvar "i")))

[<Fact>]
let ``Kind apply respects _ supertype in argument`` () =
    Assert.StrictEqual(kvar "o", applyKindExn (karrow (krow (kvar "i")) (kvar "o")) (krow (kvar "i")))
    Assert.StrictEqual(kvar "o", applyKindExn (karrow (kvar "i") (kvar "o")) KAny)
    Assert.StrictEqual(kvar "o", applyKindExn (karrow (kseq (kvar "i")) (kvar "o")) (kseq KAny))