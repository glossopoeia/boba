namespace Boba.Core

module TypeBuilder =

    open DotSeq
    open Kinds
    open Types
    open Fresh

    let mkValueType data sharing =
        typeApp (typeApp (TPrim PrValue) data) sharing
    let valueTypeData ty =
        match ty with
        | TApp (TApp (TPrim PrValue, data), _) -> data
        | _ -> failwith "Could not extract data from value type."
    let valueTypeSharing ty =
        match ty with
        | TApp (TApp (TPrim PrValue, _), sharing) -> sharing
        | _ -> failwith "Could not extract sharing from value type."

    let mkFunctionType effs perms total ins outs sharing =
        typeApp (typeApp (TPrim PrValue) (typeApp (typeApp (typeApp (typeApp (typeApp (TPrim PrFunction) effs) perms) total) ins) outs)) sharing
    let functionTypeEffs ty =
        match ty with
        | TApp (TApp (_, TApp (TApp (TApp (TApp (TApp (_, effs), _), _), _), _)), _) -> effs
        | _ -> failwith "Could not extract effects from function type."
    let functionTypePerms ty =
        match ty with
        | TApp (TApp (_, TApp (TApp (TApp (TApp (TApp (_, _), perms), _), _), _)), _) -> perms
        | _ -> failwith "Could not extract permissions from function type."
    let functionTypeTotal ty =
        match ty with
        | TApp (TApp (_, TApp (TApp (TApp (TApp (TApp (_, _), _), total), _), _)), _) -> total
        | _ -> failwith "Could not extract totality from function type."
    let functionTypeIns ty =
        match ty with
        | TApp (TApp (_, TApp (TApp (TApp (TApp (TApp (_, _), _), _), ins), _)), _) -> ins
        | _ -> failwith "Could not extract input from function type."
    let functionTypeOuts ty =
        match ty with
        | TApp (TApp (_, TApp (TApp (TApp (TApp (TApp (_, _), _), _), _), outs)), _) -> outs
        | _ -> failwith "Could not extract output from function type."
    let functionTypeSharing ty =
        match ty with
        | TApp (TApp (_, TApp (TApp (TApp (TApp (TApp (_, _), _), _), _), _)), sharing) -> sharing
        | _ -> failwith "Could not extract sharing from function type."

    let schemeSharing sch = functionTypeSharing sch.Body.Head

    let mkRowExtend elem row =
        typeApp (typeApp (TRowExtend (typeKindExn elem)) elem) row

    let schemeFromQual qType =
        { Quantified = qualFreeWithKinds qType |> Set.toList; Body = qType }

    let freshTypeVar (fresh : FreshVars) prefix kind = typeVar (fresh.Fresh prefix) kind
    let freshValVar fresh = freshTypeVar fresh "z" KValue
    let freshShareVar fresh = freshTypeVar fresh "s" KSharing
    let freshUnitVar fresh = freshTypeVar fresh "u" KUnit

    let freshValVarShare fresh = mkValueType (freshValVar fresh) (freshShareVar fresh)

    let freshFloatType fresh floatSize = typeApp (TPrim (PrFloat floatSize)) (freshUnitVar fresh)
    let freshIntType fresh intSize = typeApp (TPrim (PrInteger intSize)) (freshUnitVar fresh)
    let freshShareBoolType fresh = mkValueType (typeCon "Bool" KData) (freshShareVar fresh)
    
    let freshRefType (fresh : FreshVars) elem =
        let heap = typeVar (fresh.Fresh "h") KHeap
        let refShare = freshShareVar fresh
        let elemShare = valueTypeSharing elem
        mkValueType (typeApp (typeApp (TPrim PrRef) heap) elem) (TOr (elemShare, refShare))