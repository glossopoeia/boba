module SubstitutionTests

open Xunit
open Boba.Core.DotSeq
open Boba.Core.Fresh
open Boba.Core.Kinds
open Boba.Core.Types
open Boba.Core.TypeBuilder

[<Fact>]
let ``Kind of sequence`` () =
    let seq1 = typeSeq (ind (typeCon "s" primValueKind) SEnd)
    let seq2 = typeSeq (ind (typeCon "s" primValueKind) (ind (typeCon "t" primValueKind) SEnd))
    Assert.StrictEqual(kseq primValueKind, typeKindExn seq1)
    Assert.StrictEqual(kseq primValueKind, typeKindExn seq2)

[<Fact>]
let ``Kind of empty sequence`` () =
    Assert.StrictEqual(kseq KAny, typeKindExn (typeSeq SEnd))
    Assert.StrictEqual(kseq KAny, typeKindExn (typeSeq SEnd))
    Assert.StrictEqual(kseq KAny, typeKindExn (typeSeq SEnd))

[<Fact>]
let ``Invalid kind of sequence`` () =
    let invalidSeq = typeSeq (ind (typeCon "s" primValueKind) (ind (typeCon "t" primDataKind) SEnd))
    Assert.Throws<KindNotExpected>(fun () -> typeKindExn invalidSeq |> ignore)

[<Fact>]
let ``Compute value kind`` () =
    let valType = mkValueType (typeVar "d" primDataKind) (typeVar "s" primSharingKind)
    Assert.StrictEqual(primValueKind, typeKindExn valType)

[<Fact>]
let ``Compute constraint kind`` () =
    let qual = qualType (ind (typeCon "C" primConstraintKind) SEnd) (typeVar "v" primValueKind)
    Assert.StrictEqual(primValueKind, typeKindExn qual)

[<Fact>]
let ``Compute fn kind`` () =
    let fn =
        try
            typeKindExn 
                (mkFunctionType
                (typeVar "e" (krow primEffectKind))
                (typeVar "p" (krow primPermissionKind))
                (typeVar "t" primTotalityKind)
                (typeSeq (dot (typeVar "z" primValueKind) SEnd))
                (typeSeq (dot (typeVar "z" primValueKind) SEnd)))
        with
        | KindApplyArgMismatch (l, r) -> karrow l r
    Assert.StrictEqual(primDataKind, fn)