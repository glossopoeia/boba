namespace Boba.Core

module TypeBuilder =

    open DotSeq
    open Kinds
    open Types
    open Fresh

    let DataVarPrefix = "d"
    let TrustedVarPrefix = "v"
    let ShareVarPrefix = "s"
    let ClearanceVarPrefix = "k"
    let EffVarPrefix = "e"
    let HeapVarPrefix = "h"
    let PermVarPrefix = "p"
    let TotalVarPrefix = "q"
    let FieldVarPrefix = "f"
    let FixedVarPrefix = "x"
    let UnitVarPrefix = "u"
    let ValueVarPrefix = "t"
    let RowVarPrefix = "r"
    let CtorVarPrefix = "c"
    let SeqVarPrefix = "z"

    let typeVarPrefix kind =
        match kind with
        | KArrow _ -> CtorVarPrefix
        | KSeq _ -> SeqVarPrefix
        | _ when kind = primDataKind -> DataVarPrefix
        | _ when kind = primSharingKind -> ShareVarPrefix
        | _ when kind = primValueKind -> ValueVarPrefix
        | _ when kind = primEffectKind -> EffVarPrefix
        | _ when kind = primPermissionKind -> PermVarPrefix
        | _ when kind = primTotalityKind -> TotalVarPrefix
        | _ when kind = primMeasureKind -> UnitVarPrefix
        | _ when kind = primHeapKind -> HeapVarPrefix
        | _ when kind = primTrustKind -> TrustedVarPrefix
        | _ when kind = primClearanceKind -> ClearanceVarPrefix
        | _ when kind = primFixedKind -> FixedVarPrefix
        | _ when kind = primFieldKind -> FieldVarPrefix
        | KRow k when k = primEffectKind -> EffVarPrefix
        | KRow k when k = primPermissionKind -> PermVarPrefix
        | KRow k when k = primFieldKind -> FieldVarPrefix
        | _ -> failwith $"Tried to get prefix for non-var kind {kind}"

    let mkTypeVar ext kind = typeVar ((typeVarPrefix kind) + ext) kind

    /// Create a variable with the given name and kind `Trust`
    let trustVar name = typeVar name primTrustKind
    /// Create a variable with the given name and kind `Sharing`
    let shareVar name = typeVar name primSharingKind
    /// Create a variable with the given name and kind `Clearance`
    let clearVar name = typeVar name primClearanceKind
    /// Create a variable with the given name and kind `Value`
    let valueVar name = typeVar name primValueKind

    let rec applyTypeArgs ty args =
        match args with
        | [] -> ty
        | t :: ts -> TApp (applyTypeArgs ty ts, t)

    /// Create a type of kind Constraint with the given type arguments
    let typeConstraint name tys =
        let kind = Seq.foldBack (fun t k -> karrow (typeKindExn t) k) tys primConstraintKind
        applyTypeArgs (typeCon name kind) tys
    
    // Extract the type constructor and the arguments of a (potentially partially) constructed type.
    let rec constructedTypeComponents ty =
        match ty with
        | TApp (l, r) ->
            let constr, args = constructedTypeComponents l
            constr, List.append args [r]
        | _ -> ty, []

    /// Extract the constraint name and argument of a constraint type.
    let rec typeConstraintComponents ty =
        match ty with
        | TApp (l, r) ->
            let constr, args = typeConstraintComponents l
            constr, List.append args [r]
        | TCon (c, k) -> TCon (c, k), []
        | _ -> failwith $"Could not extract constraint components from type {ty}"

    /// Extract the name of a constraint type, i.e. the `Eq?` in `Eq? a`
    let typeConstraintName = typeConstraintComponents >> fst

    /// Extract the argument of a constraint type, i.e. the `a` in `Eq? a`
    let typeConstraintArg = typeConstraintComponents >> snd

    /// All value types in Boba have two components:
    /// 1) the data representation/format (inner, kind `Data`)
    /// 2) the sharing attribute (outer, kind `Sharing`)
    /// 
    /// These components each have a different kind to distinguish them
    /// during type inference/checking, to improve separation and prevent
    /// mistakes in the implementation of inference/checking, and to drive
    /// unification during type inference.
    let mkValueType data sharing =
        assert (typeKindExn data = primDataKind)
        assert (typeKindExn sharing = primSharingKind)
        typeApp (typeApp primTrackedCtor data) sharing

    let valueTypeComponents ty =
        match ty with
        | TApp (TApp (TCon (PrimTrackedCtorName, _), data), sharing) ->
            {| Data = data; Sharing = sharing |}
        | _ -> failwith $"Could not extract value type components from type {ty}"
    
    /// Extract the data component from a value type.
    let valueTypeData ty = (valueTypeComponents ty).Data

    /// Extract the sharing attribute component from a value type.
    let valueTypeSharing ty = (valueTypeComponents ty).Sharing

    let updateValueTypeData ty data =
        mkValueType data (valueTypeSharing ty)

    let updateValueTypeSharing ty sharing =
        mkValueType (valueTypeData ty) sharing
    
    let updateQualTypeHead ty head =
        qualType (qualTypeContext ty) head

    let removeSeqPoly seq =
        if DotSeq.length seq > 0
        then
            if DotSeq.length (DotSeq.dotted seq) > 0
            then DotSeq.init seq
            else seq
        else seq

    /// Function types are the meat and potatoes of Boba, the workhorse
    /// that encodes a lot of the interesting information about a function
    /// and what it does. All function types are value types and so share
    /// the components of a value type, but the data component is the most
    /// interesting in how it differs from other value types. Each function
    /// type data component in Boba has 5 sub-components:
    /// 1) The effects actioned but not handled by the function expression (inner, kind Effect)
    /// 2) The permissions required but not dispatched by the function expression (2nd, kind Permission)
    /// 3) The totality (whether the function is known to always terminate) (3rd, kind Totality)
    /// 4) The input value sequence required for the expression to complete (4th, kind Seq Value)
    /// 5) The output value sequence returned when the expression completes (outer, kind Seq Value)
    /// 
    /// The sharing attribute is dependent on the values the function closure contains.
    /// A closure value that refers to a value variable marked as unique must also be marked as unique.
    let mkFunctionType effs perms total ins outs =
        typeApp (typeApp (typeApp (typeApp (typeApp primFuctionCtor effs) perms) total) ins) outs
    
    /// Convenience function for defining a function value type in one call.
    let mkFunctionValueType effs perms total ins outs sharing =
        mkValueType (mkFunctionType effs perms total ins outs) sharing

    /// Expressions almost always have fixed attributes: trusted, cleared, and shared.
    /// When they don't, we manually override them in specific scenarios as part of
    /// closure typing. So this convenience function is used in most of inference, which
    /// doesn't do a lot with closures.
    let mkExpressionType effs perms total ins outs =
        mkFunctionValueType effs perms total ins outs sharedAttr
    
    let isFunctionValueType ty =
        match (valueTypeData ty) with
        | TApp (TApp (TApp (TApp (TApp (TCon (PrimFunctionCtorName, _), e), p), t), i), o) -> true
        | _ -> false

    /// Extract all the function data type components of the function value type.
    /// 0. Effect component
    /// 1. Permission component
    /// 2. Totality component
    /// 3. Input sequence
    /// 4. Output sequence
    let functionValueTypeComponents fnTy =
        match (valueTypeData fnTy) with
        | TApp (TApp (TApp (TApp (TApp (TCon (PrimFunctionCtorName, _), e), p), t), i), o) -> (e, p, t, i, o)
        | _ -> failwith "Could not extract function type components, not a valid function value type."
    
    let functionValueTypeEffect fnTy =
        match functionValueTypeComponents fnTy with
        | (e, _, _, _, _) -> e

    let functionValueTypeIns fnTy =
        match functionValueTypeComponents fnTy with
        | (_, _, _, TSeq is, _) -> is
    
    let functionValueTypeOuts fnTy =
        match functionValueTypeComponents fnTy with
        | (_, _, _, _, TSeq os) -> os

    let updateFunctionValueTypeEffect fnTy eff =
        let (_, p, t, i, o) = functionValueTypeComponents fnTy
        updateValueTypeData fnTy (mkFunctionType eff p t i o)
    
    let removeStackPolyFunctionType fnTy =
        let e, p, t, TSeq i, TSeq o = functionValueTypeComponents fnTy
        mkFunctionType e p t (typeSeq (removeSeqPoly i)) (typeSeq (removeSeqPoly o))
    
    let mkStringValueType trust clearance sharing =
        mkValueType (typeApp (typeApp primStringCtor trust) clearance) sharing
    
    let mkRuneValueType trust clearance sharing =
        mkValueType (typeApp (typeApp primRuneCtor trust) clearance) sharing

    let mkListType elem sharing =
        mkValueType (typeApp primListCtor elem) sharing
    
    let mkTupleType elems sharing =
        mkValueType (typeApp primTupleCtor (typeSeq elems)) sharing

    let mkRowExtend elem row =
        typeApp (typeApp (TRowExtend (typeKindExn elem)) elem) row

    let rowHead row =
        match row with
        | TApp (TApp (TRowExtend _, head), _) -> head
        | _ -> failwith $"Could not extract row type head from {row}"

    let mkFieldRowExtend name elem row = mkRowExtend (typeField name elem) row

    let mkPermRowExtend name row = mkRowExtend (TCon (name, primPermissionKind)) row
    
    let mkRecordValueType row sharing =
        mkValueType (typeApp primRecordCtor row) sharing
    
    let mkVariantValueType row sharing =
        mkValueType (typeApp primVariantCtor row) sharing

    let mkRefValueType heap elem sharing =
        mkValueType (typeApp (typeApp primRefCtor heap) elem) sharing
    
    let rowTypeTail row =
        match row with
        | TApp (TApp (TRowExtend _, _), tail) -> tail
        | _ -> failwith $"Expected row type with one element head, but got {row}"

    let schemeSharing sch = valueTypeSharing (snd (qualTypeComponents sch.Body))

    let schemeFromType qType =
        { QuantifiedKinds = typeKindsFree qType |> Set.toList; QuantifiedTypes = typeFreeWithKinds qType |> Set.toList; Body = qType }

    let freshTypeVar (fresh : FreshVars) kind = typeVar (fresh.Fresh (typeVarPrefix kind)) kind
    let freshDotVar (fresh : FreshVars) kind = TDotVar (fresh.Fresh (typeVarPrefix kind), kind)
    let freshDataVar fresh = freshTypeVar fresh primDataKind
    let freshTrustVar fresh = freshTypeVar fresh primTrustKind
    let freshClearVar fresh = freshTypeVar fresh primClearanceKind
    let freshShareVar fresh = freshTypeVar fresh primSharingKind
    let freshValueVar fresh = freshTypeVar fresh primValueKind
    let freshUnitVar fresh = freshTypeVar fresh primMeasureKind
    let freshEffectVar fresh = freshTypeVar fresh (KRow primEffectKind)
    let freshFieldVar fresh = freshTypeVar fresh (KRow primFieldKind)
    let freshHeapVar fresh = freshTypeVar fresh primHeapKind
    let freshPermVar fresh = freshTypeVar fresh (KRow primPermissionKind)
    let freshTotalVar fresh = freshTypeVar fresh primTotalityKind
    let freshSequenceVar fresh = SDot (freshTypeVar fresh primValueKind, SEnd)

    let freshValueComponentType fresh =
        mkValueType (freshDataVar fresh) (freshShareVar fresh)

    let freshFunctionAttributes (fresh : FreshVars) =
        (freshEffectVar fresh, freshPermVar fresh, freshTotalVar fresh)

    let mkNumericType size measure = typeApp (primNumericCtor size) measure

    let freshFloatValueType fresh floatSize =
        mkValueType (mkNumericType floatSize (TAbelianOne primMeasureKind)) (freshShareVar fresh)
    let freshIntValueType fresh intSize =
        mkValueType (mkNumericType intSize (TAbelianOne primMeasureKind)) (freshShareVar fresh)
    let freshStringValueType fresh trust clear =
        mkStringValueType trust clear (freshShareVar fresh)
    let freshRuneValueType fresh trust clear =
        mkRuneValueType trust clear (freshShareVar fresh)
    let freshBoolValueType fresh =
        mkValueType (primBoolType) (freshShareVar fresh)
    
    let rec freshenRowVar fresh row =
        match row with
        | TApp (TApp (TRowExtend k, h), tail) ->
            typeApp (typeApp (TRowExtend k) h) (freshenRowVar fresh tail)
        | TVar _ -> freshEffectVar fresh
        | _ -> failwith "Invalid row effect type encountered while trying to replace row var."