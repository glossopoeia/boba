namespace Boba.Core

module TypeBuilder =

    open DotSeq
    open Kinds
    open Types
    open Fresh

    let DataVarPrefix = "d"
    let ValidityVarPrefix = "v"
    let ShareVarPrefix = "s"
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
        | KData -> DataVarPrefix
        | KValidity -> ValidityVarPrefix
        | KSharing -> ShareVarPrefix
        | KHeap -> HeapVarPrefix
        | KTotality -> TotalVarPrefix
        | KFixed -> FixedVarPrefix
        | KUnit -> UnitVarPrefix
        | KValue -> ValueVarPrefix
        | KRow KEffect -> EffVarPrefix
        | KRow KPermission -> PermVarPrefix
        | KRow KField -> FieldVarPrefix
        | KArrow _ -> CtorVarPrefix
        | KSeq _ -> SeqVarPrefix
        | _ -> failwith "Tried to get prefix for non-var kind"

    let mkTypeVar ext kind = typeVar ((typeVarPrefix kind) + ext) kind

    let validityVar name = typeVar name KValidity
    let shareVar name = typeVar name KSharing
    let unitVar name = typeVar name KUnit

    /// All value types in Boba have three components:
    /// 1) the data representation/format (inner, kind Data)
    /// 2) the validity attribute (middle, kind Validity)
    /// 3) the sharing attribute (outer, kind Sharing)
    /// 
    /// Each of these components has a different kind to distinguish them
    /// during type inference/checking, to improve separation and prevent
    /// mistakes in the implementation of inference/checking, and to drive
    /// unification during type inference.
    let mkValueType data validity sharing =
        assert (typeKindExn data = KData)
        assert (typeKindExn validity = KValidity)
        assert (typeKindExn sharing = KSharing)
        typeApp (typeApp (typeApp (TPrim PrValue) data) validity) sharing
    
    let mkValueTotalShared data =
        mkValueType data validAttr sharedAttr

    /// Extract the data component from a value type.
    let valueTypeData ty =
        match ty with
        | TApp (TApp (TApp (TPrim PrValue, data), _), _) -> data
        | _ -> failwith $"Could not extract data from value type {ty}."

    /// Extract the validity attribute component from a value type.
    let valueTypeValidity ty =
        match ty with
        | TApp (TApp (TApp (TPrim PrValue, _), validity), _) -> validity
        | _ -> failwith $"Could not extract sharing from value type {ty}."

    /// Extract the sharing attribute component from a value type.
    let valueTypeSharing ty =
        match ty with
        | TApp (TApp (TApp (TPrim PrValue, _), _), sharing) -> sharing
        | _ -> failwith $"Could not extract sharing from value type {ty}."

    let updateValueTypeData ty data =
        mkValueType data (valueTypeValidity ty) (valueTypeSharing ty)

    let updateValueTypeSharing ty sharing =
        mkValueType (valueTypeData ty) (valueTypeValidity ty) sharing

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
    /// For the other two attributes, a couple special conditions apply:
    /// 1) The validity attribute is almost always Validated (True), since user input can never contruct
    ///    a function value. While closures may have access to Unvalidated data, that does not mean
    ///    that the function itself is Unvalidated. The only time a function type is Unvalidated is when
    ///    a module is imported as untrusted or when a function value comes from a dynamically loaded library.
    /// 2) The sharing attribute, unlike validity, is dependent on the values the function closure contains.
    ///    So a closure value that refers to a value variable marked as unique must also be marked as unique.
    let mkFunctionType effs perms total ins outs =
        typeApp (typeApp (typeApp (typeApp (typeApp (TPrim PrFunction) effs) perms) total) ins) outs
    
    /// Convenience function for defining a function value type in one call.
    let mkFunctionValueType effs perms total ins outs validity sharing =
        mkValueType (mkFunctionType effs perms total ins outs) validity sharing
    
    let isFunctionValueType ty =
        match (valueTypeData ty) with
        | TApp (TApp (TApp (TApp (TApp (TPrim PrFunction, e), p), t), i), o) -> true
        | _ -> false

    /// Extract all the function data type components of the function value type.
    /// 0. Effect component
    /// 1. Permission component
    /// 2. Totality component
    /// 3. Input sequence
    /// 4. Output sequence
    let functionValueTypeComponents fnTy =
        match (valueTypeData fnTy) with
        | TApp (TApp (TApp (TApp (TApp (TPrim PrFunction, e), p), t), i), o) -> (e, p, t, i, o)
        | _ -> failwith "Could not extract function type components, not a valid function value type."
    
    let functionValueTypeEffect fnTy =
        match functionValueTypeComponents fnTy with
        | (e, _, _, _, _) -> e

    let functionValueTypeIns fnTy =
        match functionValueTypeComponents fnTy with
        | (_, _, _, is, _) -> is
    
    let functionValueTypeOuts fnTy =
        match functionValueTypeComponents fnTy with
        | (_, _, _, _, os) -> os

    let updateFunctionValueTypeEffect fnTy eff =
        let (_, p, t, i, o) = functionValueTypeComponents fnTy
        updateValueTypeData fnTy (mkFunctionType eff p t i o)

    let mkListType elem validity sharing =
        mkValueType (typeApp (TPrim PrList) elem) validity sharing

    let mkRowExtend elem row =
        typeApp (typeApp (TRowExtend (typeKindExn elem)) elem) row

    let mkFieldRowExtend name elem row = mkRowExtend (typeField name elem) row
    
    let mkRecordValueType row validity sharing =
        mkValueType (typeApp (TPrim PrRecord) row) validity sharing
    
    let mkVariantValueType row validity sharing =
        mkValueType (typeApp (TPrim PrVariant) row) validity sharing
    
    let rowTypeTail row =
        match row with
        | TApp (TApp (TRowExtend _, _), tail) -> tail
        | _ -> failwith $"Expected row type with one element head, but got {row}"

    let schemeSharing sch = valueTypeSharing sch.Body.Head

    let schemeFromQual qType =
        { Quantified = qualFreeWithKinds qType |> Set.toList; Body = qType }

    let freshTypeVar (fresh : FreshVars) kind = typeVar (fresh.Fresh (typeVarPrefix kind)) kind
    let freshDataVar fresh = freshTypeVar fresh KData
    let freshValidityVar fresh = freshTypeVar fresh KValidity
    let freshShareVar fresh = freshTypeVar fresh KSharing
    let freshValueVar fresh = freshTypeVar fresh KValue
    let freshUnitVar fresh = freshTypeVar fresh KUnit
    let freshEffectVar fresh = freshTypeVar fresh (KRow KEffect)
    let freshFieldVar fresh = freshTypeVar fresh (KRow KField)
    let freshHeapVar fresh = freshTypeVar fresh KHeap
    let freshPermVar fresh = freshTypeVar fresh (KRow KPermission)
    let freshTotalVar fresh = freshTypeVar fresh KTotality
    let freshSequenceVar fresh = SDot (freshTypeVar fresh KValue, SEnd)

    let freshValueComponentType fresh =
        mkValueType (freshDataVar fresh) (freshValidityVar fresh) (freshShareVar fresh)

    let freshFunctionAttributes (fresh : FreshVars) =
        (freshEffectVar fresh, freshPermVar fresh, freshTotalVar fresh)

    let freshFloatType fresh floatSize = typeApp (TPrim (PrFloat floatSize)) (freshUnitVar fresh)
    let freshIntType fresh intSize = typeApp (TPrim (PrInteger intSize)) (freshUnitVar fresh)

    let freshFloatValueType fresh floatSize validity =
        mkValueType (freshFloatType fresh floatSize) validity (freshShareVar fresh)
    let freshIntValueType fresh intSize validity =
        mkValueType (freshIntType fresh intSize) validity (freshShareVar fresh)
    let freshStringValueType fresh validity =
        mkValueType (typeCon "String" KData) validity (freshShareVar fresh)
    let freshBoolValueType fresh validity =
        mkValueType (TPrim PrBool) validity (freshShareVar fresh)
    
    let freshRefValueType (fresh : FreshVars) elem =
        assert (typeKindExn elem = KValue)

        let heap = freshHeapVar fresh
        let refShare = freshShareVar fresh
        let refValid = freshValidityVar fresh
        let data = typeApp (typeApp (TPrim PrRef) heap) elem
        mkValueType data (TAnd (valueTypeValidity elem, refValid)) (TOr (valueTypeSharing elem, refShare))