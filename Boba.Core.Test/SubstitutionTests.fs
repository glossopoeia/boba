module SubstitutionTests

open Xunit
open Boba.Core.DotSeq
open Boba.Core.Fresh
open Boba.Core.Kinds
open Boba.Core.Types

[<Fact>]
let ``Kind of sequence`` () =
    let seq1 = typeSeq (ind (typeCon "s" primValueKind) SEnd) primValueKind
    let seq2 = typeSeq (ind (typeCon "s" primValueKind) (ind (typeCon "t" primValueKind) SEnd)) primValueKind
    Assert.StrictEqual(kseq primValueKind, typeKindExn seq1)
    Assert.StrictEqual(kseq primValueKind, typeKindExn seq2)

[<Fact>]
let ``Invalid kind of sequence`` () =
    let invalidSeq = typeSeq (ind (typeCon "s" primValueKind) (ind (typeCon "t" primDataKind) SEnd)) primValueKind
    Assert.Throws<KindNotExpected>(fun () -> typeKindExn invalidSeq |> ignore)