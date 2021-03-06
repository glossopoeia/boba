module InferenceTests

open Xunit
open Boba.Core.DotSeq
open Boba.Core.Fresh
open Boba.Core.Expression
open Boba.Core.Inference
open Boba.Core.Kinds
open Boba.Core.Types

[<Fact>]
let ``Inference Succeed: 2 2 ==> (a... --> a... int int)`` () =
    let inferred = inferTop (new SimpleFresh(0)) () [WInteger 2; WInteger 2]
    Assert.StrictEqual(
        mkFunctionType
            (typeVar "e" (KRow KEffect))
            (typeVar "p" (KRow KPermission))
            (typeVar "t" KTotality)
            (TSeq (SDot (typeVar "a" KValue, SEnd)))
            (TSeq
                (SInd (mkValueType (typeApp (TPrim PrInt32) (typeVar "u" KUnit)) (typeVar "s" KSharing),
                    (SInd (mkValueType (typeApp (TPrim PrInt32) (typeVar "u" KUnit)) (typeVar "s" KSharing),
                        SDot (typeVar "a" KValue, SEnd))))))
            (TFalse KSharing),
        inferred.Head)

[<Fact>]
let ``Inference Failed: if then "hello" else 2`` () =
    Assert.ThrowsAny<System.Exception>(fun () -> inferTop (new SimpleFresh(0)) () [WIf ([WString "hello"],[WInteger 2])] |> ignore)

[<Fact>]
let ``Inference Succeed: if then 3 else 2`` () =
    let inferred = inferTop (new SimpleFresh(0)) () [WIf ([WInteger 3],[WInteger 2])]
    Assert.StrictEqual(
        mkFunctionType
            (typeVar "e" (KRow KEffect))
            (typeVar "p" (KRow KPermission))
            (typeVar "t" KTotality)
            (TSeq (SInd (mkValueType (TPrim PrBool) (typeVar "s" KSharing), (SDot (typeVar "a" KValue, SEnd)))))
            (TSeq (SInd (mkValueType (typeApp (TPrim PrInt32) (typeVar "u" KUnit)) (typeVar "s" KSharing), SDot (typeVar "a" KValue, SEnd))))
            (TFalse KSharing),
        inferred.Head)