module InferenceTests

open Xunit
open Boba.Core.DotSeq
open Boba.Core.Fresh
open Boba.Core.Expression
open Boba.Core.Inference
open Boba.Core.Kinds
open Boba.Core.Types
open Boba.Core.TypeBuilder
open Boba.Core


(* [<Fact>]
let ``Inference Succeed: 2 2 ==> (a... --> a... int int)`` () =
    let inferred = inferTop (new SimpleFresh(0)) Environment.empty [WInteger ("2", I32); WInteger ("2", I32)]
    Assert.StrictEqual(
        mkFunctionType
            (typeVar "e" (KRow KEffect))
            (typeVar "p" (KRow KPermission))
            (typeVar "t" KTotality)
            (TSeq (SDot (typeVar "a" KValue, SEnd)))
            (TSeq
                (SInd (mkValueType (typeApp (TPrim (PrInteger I32)) (typeVar "u" KUnit)) (typeVar "s" KSharing),
                    (SInd (mkValueType (typeApp (TPrim (PrInteger I32)) (typeVar "u" KUnit)) (typeVar "s" KSharing),
                        SDot (typeVar "a" KValue, SEnd))))))
            (TFalse KSharing),
        inferred.Item1.Head)

[<Fact>]
let ``Inference Failed: if then "hello" else 2`` () =
    Assert.ThrowsAny<System.Exception>(fun () -> inferTop (new SimpleFresh(0)) Environment.empty [WIf ([WString "hello"],[WInteger ("2", I32)])] |> ignore)

[<Fact>]
let ``Inference Succeed: if then 3 else 2`` () =
    let inferred = inferTop (new SimpleFresh(0)) Environment.empty [WIf ([WInteger ("3", I32)],[WInteger ("2", I32)])]
    Assert.StrictEqual(
        mkFunctionType
            (typeVar "e" (KRow KEffect))
            (typeVar "p" (KRow KPermission))
            (typeVar "t" KTotality)
            (TSeq (SInd (mkValueType (TPrim PrBool) (typeVar "s" KSharing), (SDot (typeVar "a" KValue, SEnd)))))
            (TSeq (SInd (mkValueType (typeApp (TPrim (PrInteger I32)) (typeVar "u" KUnit)) (typeVar "s" KSharing), SDot (typeVar "a" KValue, SEnd))))
            (TFalse KSharing),
        inferred.Item1.Head) *)
