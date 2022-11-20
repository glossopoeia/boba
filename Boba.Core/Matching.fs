﻿namespace Boba.Core

module Matching =
    
    open Common
    open Fresh
    open Kinds
    open Types

    type KindConstraint =
        {
            LeftKind: Kind;
            RightKind: Kind
        }
        override this.ToString () = $"{this.LeftKind} = {this.RightKind}"


    type TypeConstraint =
        {
            Left: Type;
            Right: Type
        }
        override this.ToString () = $"{this.Left} = {this.Right}"
    
    let unifyConstraint l r = { Left = l; Right = r }

    let constraintSubstExn fresh subst constr = {
        Left = typeSubstSimplifyExn fresh subst constr.Left;
        Right = typeSubstSimplifyExn fresh subst constr.Right
    }

    let kindConstraintSubst subst constr = {
        LeftKind = kindSubst subst constr.LeftKind;
        RightKind = kindSubst subst constr.RightKind
    }



    let rec genSplitSub (fresh: FreshVars) vars =
        match vars with
        | [] -> Map.empty
        | (x, k) :: xs ->
            let freshInd = fresh.Fresh x
            let freshSeq = fresh.Fresh x
            let sub = genSplitSub fresh xs
            Map.add x (TSeq (DotSeq.SInd (typeVar freshInd k, (DotSeq.SDot (typeVar freshSeq k, DotSeq.SEnd))))) sub


    // One-way matching of types
    exception MatchKindMismatch of Kind * Kind
    exception MatchBooleanMismatch of Type * Type
    exception MatchAbelianMismatch of Type * Type
    exception MatchRowMismatch of Type * Type
    exception MatchStructuralMismatch of Type * Type
    exception MatchSequenceMismatch of DotSeq.DotSeq<Type> * DotSeq.DotSeq<Type>
    exception MatchNonValueSequence of Type * Type

    /// Convenience function for getting the shared set of labels in two lists
    let overlappingLabels left right = Set.intersect (Set.ofList left) (Set.ofList right)
    
    let decomposeMatchingLabel label leftRow rightRow =
        let rec decomposeOnLabel acc fs =
            match fs with
            | f :: fs when rowElementHead f = label -> (f, List.append acc fs)
            | f :: fs -> decomposeOnLabel (f :: acc) fs
            | [] -> failwith $"Internal error: expected to find field {label} in row"
        let (lMatched, lRest) = decomposeOnLabel [] leftRow.Elements
        let (rMatched, rRest) = decomposeOnLabel [] rightRow.Elements
        ((lMatched, rMatched), (lRest, rRest))
    
    let collectMatchingLabels label leftRow rightRow =
        let (leftWith, leftRem) = List.partition (fun e -> rowElementHead e = label) leftRow.Elements
        let (rightWith, rightRem) = List.partition (fun e -> rowElementHead e = label) rightRow.Elements
        List.append leftWith rightWith, (leftRem, rightRem)

    /// Generate a substitution `s` such that `s(l) = r`, where equality is according to the
    /// equational theory of each subterm (i.e. not necessarily syntactically equal, but always
    /// semantically equal).
    let rec typeMatchExn fresh l r =
        match (l, r) with
        | _ when l = r -> Map.empty
        | _ when not (kindEq (typeKindExn l) (typeKindExn r)) ->
            raise (MatchKindMismatch (typeKindExn l, typeKindExn r))
        | _ when isKindBoolean (typeKindExn l) || isKindBoolean (typeKindExn r) ->
            match Boolean.unify (typeToBooleanEqn l) (Boolean.rigidify (typeToBooleanEqn r)) with
            | Some subst -> mapValues (booleanEqnToType (typeKindExn l)) subst
            | None -> raise (MatchBooleanMismatch (l, r))
        | _ when typeKindExn l = primFixedKind || typeKindExn r = primFixedKind ->
            match Abelian.matchEqns fresh (typeToFixedEqn l) (typeToFixedEqn r) with
            | Some subst -> mapValues fixedEqnToType subst
            | None -> raise (MatchAbelianMismatch (l, r))
        | _ when isKindAbelian (typeKindExn l) || isKindAbelian (typeKindExn r) ->
            match Abelian.matchEqns fresh (typeToUnitEqn l) (typeToUnitEqn r) with
            | Some subst -> mapValues (abelianEqnToType (typeKindExn l)) subst
            | None -> raise (MatchAbelianMismatch (l, r))
        | _ when isKindExtensibleRow (typeKindExn l) || isKindExtensibleRow (typeKindExn r) ->
            matchRow fresh (typeToRow l) (typeToRow r)
        | TSeq ls, TSeq rs when kindEq (typeKindExn l) (typeKindExn r) ->
            typeMatchSeqExn fresh ls rs
        | TSeq _, TSeq _ ->
            raise (MatchNonValueSequence (l, r))
        | (TVar (n, _), r) -> Map.add n r Map.empty
        | (TDotVar _, _) -> failwith "Dot vars should only occur in boolean types."
        | (TApp (ll, lr), TApp (rl, rr)) ->
            mergeSubstExn fresh (typeMatchExn fresh ll rl) (typeMatchExn fresh lr rr)
        | _ ->
            raise (MatchStructuralMismatch (l, r))
    and typeMatchSeqExn fresh ls rs =
        match ls, rs with
        | DotSeq.SEnd, DotSeq.SEnd ->
            Map.empty
        | DotSeq.SInd (li, lss), DotSeq.SInd (ri, rss) ->
            let lu = typeMatchExn fresh li ri
            let ru = typeMatchExn fresh (typeSubstSimplifyExn fresh lu (typeSeq lss)) (typeSubstSimplifyExn fresh lu (typeSeq rss))
            mergeSubstExn fresh ru lu
        | DotSeq.SDot (ld, DotSeq.SEnd), DotSeq.SDot (rd, DotSeq.SEnd) ->
            typeMatchExn fresh ld rd
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SEnd ->
            [for (v, k) in List.ofSeq (typeFreeWithKinds li) do (v, typeSeq DotSeq.SEnd)] |> Map.ofList
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SInd (ri, rs) ->
            let freshVars = typeFreeWithKinds li |> List.ofSeq |> genSplitSub fresh
            let extended =
                typeMatchExn fresh
                    (typeSubstSimplifyExn fresh freshVars (typeSeq (DotSeq.SDot (li, DotSeq.SEnd))))
                    (typeSeq (DotSeq.SInd (ri, rs)))
            mergeSubstExn fresh extended freshVars
        | _ ->
            raise (MatchSequenceMismatch (ls, rs))
    and matchRow fresh leftRow rightRow =
        match leftRow.Elements, rightRow.Elements with
        | _, _ when leftRow.ElementKind <> rightRow.ElementKind ->
            raise (MatchKindMismatch (leftRow.ElementKind, rightRow.ElementKind))
        | [], [] ->
            match leftRow.RowEnd, rightRow.RowEnd with
            | Some lv, Some rv -> Map.empty.Add(lv, typeVar rv (KRow leftRow.ElementKind))
            | Some lv, None -> Map.empty.Add(lv, TEmptyRow leftRow.ElementKind)
            | None, Some _ -> raise (MatchRowMismatch (rowToType leftRow, rowToType rightRow))
            | None, None -> Map.empty
        | ls, [] ->
            raise (MatchRowMismatch (rowToType leftRow, rowToType rightRow))
        | [], rs ->
            match leftRow.RowEnd with
            | Some lv -> Map.empty.Add(lv, rowToType rightRow)
            | _ -> raise (MatchRowMismatch (rowToType leftRow, rowToType rightRow))
        | ls, rs ->
            let overlapped = overlappingLabels (List.map rowElementHead ls) (List.map rowElementHead rs)
            if not (Set.isEmpty overlapped)
            then
                let label = Set.minElement overlapped
                let ((lElem, rElem), (lRest, rRest)) = decomposeMatchingLabel label leftRow rightRow
                let fu = typeMatchExn fresh lElem rElem
                let ru = matchRow fresh { leftRow with Elements = lRest } { rightRow with Elements = rRest }
                mergeSubstExn fresh ru fu
            else raise (MatchRowMismatch (rowToType leftRow, rowToType rightRow))

    /// Returns true if the `l` type is more general than (or at least as general as)
    /// the given type for `r`.
    let isTypeMatch fresh l r =
        try
            typeMatchExn fresh l r |> constant true
        with
            | ex -> false
    

    /// Generate a substitution `s` such that `s(l) = r`, where equality is according to the
    /// equational theory of each subterm (i.e. not necessarily syntactically equal, but always
    /// semantically equal). The strictness here is that sequence variables are not expanded,
    /// i.e. they are essentially treated as individual variables.
    let rec strictTypeMatchExn fresh l r =
        match (l, r) with
        | _ when l = r -> Map.empty
        | _ when not (kindEq (typeKindExn l) (typeKindExn r)) ->
            raise (MatchKindMismatch (typeKindExn l, typeKindExn r))
        | _ when isKindBoolean (typeKindExn l) || isKindBoolean (typeKindExn r) ->
            match Boolean.unify (typeToBooleanEqn l) (Boolean.rigidify (typeToBooleanEqn r)) with
            | Some subst -> mapValues (booleanEqnToType (typeKindExn l)) subst
            | None -> raise (MatchBooleanMismatch (l, r))
        | _ when typeKindExn l = primFixedKind || typeKindExn r = primFixedKind ->
            match Abelian.matchEqns fresh (typeToFixedEqn l) (typeToFixedEqn r) with
            | Some subst -> mapValues fixedEqnToType subst
            | None -> raise (MatchAbelianMismatch (l, r))
        | _ when isKindAbelian (typeKindExn l) || isKindAbelian (typeKindExn r) ->
            match Abelian.matchEqns fresh (typeToUnitEqn l) (typeToUnitEqn r) with
            | Some subst -> mapValues (abelianEqnToType (typeKindExn l)) subst
            | None -> raise (MatchAbelianMismatch (l, r))
        | _ when isKindExtensibleRow (typeKindExn l) || isKindExtensibleRow (typeKindExn r) ->
            strictMatchRow fresh (typeToRow l) (typeToRow r)
        | TSeq ls, TSeq rs when typeKindExn (TSeq ls) = typeKindExn (TSeq rs) ->
            strictTypeMatchSeqExn fresh ls rs
        | TSeq _, TSeq _ ->
            raise (MatchNonValueSequence (l, r))
        | (TVar (n, _), r) -> Map.add n r Map.empty
        | (TDotVar _, _) -> failwith "Dot vars should only occur in boolean types."
        | (TApp (ll, lr), TApp (rl, rr)) ->
            mergeSubstExn fresh (strictTypeMatchExn fresh ll rl) (strictTypeMatchExn fresh lr rr)
        | _ ->
            raise (MatchStructuralMismatch (l, r))
    and strictTypeMatchSeqExn fresh ls rs =
        match ls, rs with
        | DotSeq.SEnd, DotSeq.SEnd ->
            Map.empty
        | DotSeq.SInd (li, lss), DotSeq.SInd (ri, rss) ->
            let lu = strictTypeMatchExn fresh li ri
            let ru = strictTypeMatchExn fresh (typeSubstSimplifyExn fresh lu (typeSeq lss)) (typeSubstSimplifyExn fresh lu (typeSeq rss))
            mergeSubstExn fresh ru lu
        | DotSeq.SDot (ld, DotSeq.SEnd), DotSeq.SDot (rd, DotSeq.SEnd) ->
            strictTypeMatchExn fresh ld rd
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SEnd ->
            [for (v, k) in List.ofSeq (typeFreeWithKinds li) do (v, typeSeq DotSeq.SEnd)] |> Map.ofList
        | _ ->
            raise (MatchSequenceMismatch (ls, rs))
    and strictMatchRow fresh leftRow rightRow =
        match leftRow.Elements, rightRow.Elements with
        | _, _ when leftRow.ElementKind <> rightRow.ElementKind ->
            raise (MatchKindMismatch (leftRow.ElementKind, rightRow.ElementKind))
        | [], [] ->
            match leftRow.RowEnd, rightRow.RowEnd with
            | Some lv, Some rv -> Map.empty.Add(lv, typeVar rv (KRow leftRow.ElementKind))
            | Some lv, None -> Map.empty.Add(lv, TEmptyRow leftRow.ElementKind)
            | None, Some _ -> raise (MatchRowMismatch (rowToType leftRow, rowToType rightRow))
            | None, None -> Map.empty
        | ls, [] ->
            raise (MatchRowMismatch (rowToType leftRow, rowToType rightRow))
        | [], rs ->
            match leftRow.RowEnd with
            | Some lv -> Map.empty.Add(lv, rowToType rightRow)
            | _ -> raise (MatchRowMismatch (rowToType leftRow, rowToType rightRow))
        | ls, rs ->
            let overlapped = overlappingLabels (List.map rowElementHead ls) (List.map rowElementHead rs)
            if not (Set.isEmpty overlapped)
            then
                let label = Set.minElement overlapped
                let ((lElem, rElem), (lRest, rRest)) = decomposeMatchingLabel label leftRow rightRow
                let fu = strictTypeMatchExn fresh lElem rElem
                let ru = strictMatchRow fresh { leftRow with Elements = lRest } { rightRow with Elements = rRest }
                mergeSubstExn fresh ru fu
            else raise (MatchRowMismatch (rowToType leftRow, rowToType rightRow))
    
    /// Returns true if the `l` type is more general than (or at least as general as)
    /// the given type for `r`, without expanding sequence variables.
    let isStrictTypeMatch fresh l r =
        try
            strictTypeMatchExn fresh l r |> constant true
        with
            | ex -> false