namespace Boba.Core

module Unification =
    
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

    let constraintSubstExn subst constr = {
        Left = typeSubstSimplifyExn subst constr.Left;
        Right = typeSubstSimplifyExn subst constr.Right
    }

    let kindConstraintSubst subst constr = {
        LeftKind = kindSubst subst constr.LeftKind;
        RightKind = kindSubst subst constr.RightKind
    }



    let rec genSplitSub (fresh: FreshVars) vars =
        match vars with
        | [] -> Map.empty
        | x :: xs ->
            let freshInd = fresh.Fresh x
            let freshSeq = fresh.Fresh x
            let sub = genSplitSub fresh xs
            Map.add x (TSeq (DotSeq.SInd (typeVar freshInd KValue, (DotSeq.SDot (typeVar freshSeq KValue, DotSeq.SEnd))), KValue)) sub


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
        | _ when typeKindExn l <> typeKindExn r -> raise (MatchKindMismatch (typeKindExn l, typeKindExn r))
        | _ when isKindBoolean (typeKindExn l) ->
            match Boolean.unify (typeToBooleanEqn l) (Boolean.rigidify (typeToBooleanEqn r)) with
            | Some subst -> mapValues (booleanEqnToType (typeKindExn l)) subst
            | None -> raise (MatchBooleanMismatch (l, r))
        | _ when typeKindExn l = KFixed ->
            match Abelian.matchEqns fresh (typeToFixedEqn l) (typeToFixedEqn r) with
            | Some subst -> mapValues fixedEqnToType subst
            | None -> raise (MatchAbelianMismatch (l, r))
        | _ when typeKindExn l = KUnit ->
            match Abelian.matchEqns fresh (typeToUnitEqn l) (typeToUnitEqn r) with
            | Some subst -> mapValues unitEqnToType subst
            | None -> raise (MatchAbelianMismatch (l, r))
        | _ when isKindExtensibleRow (typeKindExn l) ->
            matchRow fresh (typeToRow l) (typeToRow r)
        | _ when isKindSet (typeKindExn l) ->
            matchRow fresh (typeToRow l) (typeToRow r)
        | TSeq (ls, lk), TSeq (rs, rk) when lk = rk ->
            typeMatchSeqExn fresh ls rs
        | TSeq _, TSeq _ ->
            raise (MatchNonValueSequence (l, r))
        | (TVar (n, _), r) -> Map.add n r Map.empty
        | (TDotVar _, _) -> failwith "Dot vars should only occur in boolean types."
        | (TApp (ll, lr), TApp (rl, rr)) ->
            mergeSubstExn (typeMatchExn fresh ll rl) (typeMatchExn fresh lr rr)
        | _ ->
            raise (MatchStructuralMismatch (l, r))
    and typeMatchSeqExn fresh ls rs =
        match ls, rs with
        | DotSeq.SEnd, DotSeq.SEnd ->
            Map.empty
        | DotSeq.SInd (li, lss), DotSeq.SInd (ri, rss) ->
            let lu = typeMatchExn fresh li ri
            let ru = typeMatchExn fresh (typeSubstExn lu (TSeq (lss, KValue))) (typeSubstExn lu (TSeq (rss, KValue)))
            mergeSubstExn ru lu
        | DotSeq.SDot (ld, DotSeq.SEnd), DotSeq.SDot (rd, DotSeq.SEnd) ->
            typeMatchExn fresh ld rd
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SEnd ->
            [for v in List.ofSeq (typeFree li) do (v, TSeq (DotSeq.SEnd, KValue))] |> Map.ofList
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SInd (ri, rs) ->
            let freshVars = typeFree li |> List.ofSeq |> genSplitSub fresh
            let extended = typeMatchExn fresh (typeSubstExn freshVars li) (TSeq (DotSeq.SInd (ri, rs), KValue))
            mergeSubstExn extended freshVars
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
                if leftRow.Scoped
                then
                    // scoped rows only unify the first occurence of each label in the row, allowing multiple 'scoped' labels
                    let ((lElem, rElem), (lRest, rRest)) = decomposeMatchingLabel label leftRow rightRow
                    let fu = typeMatchExn fresh lElem rElem
                    let ru = matchRow fresh { leftRow with Elements = lRest } { rightRow with Elements = rRest }
                    mergeSubstExn ru fu
                else
                    // non-scoped rows unify all occurences of each label in the row, and filter them out later in simplification
                    let elems, (lRest, rRest) = collectMatchingLabels label leftRow rightRow
                    let fUnis = Seq.pairwise elems |> Seq.map (fun (l,r) -> typeMatchExn fresh l r)
                    let fu = Seq.fold (fun unif sub -> mergeSubstExn unif sub) Map.empty fUnis
                    let ru = matchRow fresh { leftRow with Elements = lRest } { rightRow with Elements = rRest }
                    mergeSubstExn ru fu
            else raise (MatchRowMismatch (rowToType leftRow, rowToType rightRow))

    /// Returns true if the `l` type is more general than (or at least as general as)
    /// the given type for `r`.
    let isTypeMatch fresh l r =
        try
            typeMatchExn fresh l r |> constant true
        with
            | ex -> false


    // Unification of types
    exception UnifyKindMismatch of Type * Type * Kind * Kind
    exception UnifyRowKindMismatch of Kind * Kind
    exception UnifyAbelianMismatch of Type * Type
    exception UnifyBooleanMismatch of Type * Type
    exception UnifyOccursCheckFailure of Type * Type
    exception UnifyRowRigidMismatch of Type * Type
    exception UnifyRigidRigidMismatch of Type * Type
    exception UnifySequenceMismatch of DotSeq.DotSeq<Type> * DotSeq.DotSeq<Type>
    exception UnifyNonValueSequence of Type * Type

    let rec typeUnifyExn fresh l r =
        match (l, r) with
        | _ when l = r ->
            Map.empty
        | _ when typeKindExn l <> typeKindExn r ->
            raise (UnifyKindMismatch (l, r, typeKindExn l, typeKindExn r))
        | _ when isKindBoolean (typeKindExn l) ->
            match Boolean.unify (typeToBooleanEqn l) (typeToBooleanEqn r) with
            | Some subst ->
                //printfn $"Boolean unifier of {typeToBooleanEqn l} ~ {typeToBooleanEqn r}:"
                //Map.iter (fun k v -> printfn $"{k} -> {v}") subst
                mapValues (booleanEqnToType (typeKindExn l)) subst
            | None -> raise (UnifyBooleanMismatch (l, r))
        | _ when typeKindExn l = KFixed ->
            match Abelian.unify fresh (typeToFixedEqn l) (typeToFixedEqn r) with
            | Some subst -> mapValues fixedEqnToType subst
            | None -> raise (UnifyAbelianMismatch (l, r))
        | _ when typeKindExn l = KUnit ->
            match Abelian.unify fresh (typeToUnitEqn l) (typeToUnitEqn r) with
            | Some subst -> mapValues unitEqnToType subst
            | None -> raise (UnifyAbelianMismatch (l, r))
        | _ when isKindExtensibleRow (typeKindExn l) -> unifyRow fresh (typeToRow l) (typeToRow r)
        | _ when isKindSet (typeKindExn l) -> unifyRow fresh (typeToRow l) (typeToRow r)
        | TDotVar _, _ -> failwith "Dot vars should only occur in boolean types."
        | _, TDotVar _ -> failwith "Dot vars should only occur in boolean types."
        | TVar (nl, _), r when Set.contains nl (typeFree r) ->
            raise (UnifyOccursCheckFailure (l, r))
        | l, TVar (nr, _) when Set.contains nr (typeFree l) ->
            raise (UnifyOccursCheckFailure (l, r))
        | TVar (nl, _), r ->
            Map.add nl r Map.empty
        | l, TVar (nr, _) ->
            Map.add nr l Map.empty
        | TApp (ll, lr), TApp (rl, rr) ->
            let lu = typeUnifyExn fresh ll rl
            let ru = typeUnifyExn fresh (typeSubstSimplifyExn lu lr) (typeSubstSimplifyExn lu rr)
            composeSubstExn ru lu
        | TSeq (ls, lk), TSeq (rs, rk) when lk = rk && lk = KValue ->
            typeUnifySeqExn fresh ls rs
        | TSeq _, TSeq _ ->
            raise (UnifyNonValueSequence (l, r))
        | _ ->
            raise (UnifyRigidRigidMismatch (l, r))
    and typeUnifySeqExn fresh ls rs =
        match ls, rs with
        | DotSeq.SEnd, DotSeq.SEnd ->
            Map.empty
        | DotSeq.SInd (li, lss), DotSeq.SInd (ri, rss) ->
            let lu = typeUnifyExn fresh li ri
            let lssu = typeSubstSimplifyExn lu (TSeq (lss, KValue))
            let rssu = typeSubstSimplifyExn lu (TSeq (rss, KValue))
            let ru = typeUnifyExn fresh lssu rssu
            composeSubstExn ru lu
        | DotSeq.SDot (ld, DotSeq.SEnd), DotSeq.SDot (rd, DotSeq.SEnd) ->
            typeUnifyExn fresh ld rd
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SEnd ->
            [for v in List.ofSeq (typeFree li) do (v, TSeq (DotSeq.SEnd, KValue))] |> Map.ofList
        | DotSeq.SEnd, DotSeq.SDot (ri, DotSeq.SEnd) ->
            [for v in List.ofSeq (typeFree ri) do (v, TSeq (DotSeq.SEnd, KValue))] |> Map.ofList
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SInd _ when not (Set.isEmpty (Set.intersect (typeFree li) (typeFree (TSeq (rs, KValue))))) ->
            raise (UnifyOccursCheckFailure (TSeq (ls, KValue), TSeq (rs, KValue)))
        | DotSeq.SInd _, DotSeq.SDot (ri, DotSeq.SEnd) when not (Set.isEmpty (Set.intersect (typeFree ri) (typeFree (TSeq (ls, KValue))))) ->
            raise (UnifyOccursCheckFailure (TSeq (ls, KValue), TSeq (rs, KValue)))
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SInd (ri, rs) ->
            let freshVars = typeFree li |> List.ofSeq |> genSplitSub fresh
            let extended =
                typeUnifyExn fresh
                    (typeSubstSimplifyExn freshVars (TSeq (DotSeq.SDot (li, DotSeq.SEnd), KValue)))
                    (TSeq (DotSeq.SInd (ri, rs), KValue))
            composeSubstExn extended freshVars
        | DotSeq.SInd (li, ls), DotSeq.SDot (ri, DotSeq.SEnd) ->
            let freshVars = typeFree ri |> List.ofSeq |> genSplitSub fresh
            let extended =
                typeUnifyExn fresh
                    (typeSubstSimplifyExn freshVars (TSeq (DotSeq.SDot (ri, DotSeq.SEnd), KValue)))
                    (TSeq (DotSeq.SInd (li, ls), KValue))
            composeSubstExn extended freshVars
        | _ ->
            raise (UnifySequenceMismatch (ls, rs))
    and unifyRow fresh leftRow rightRow =
        match leftRow.Elements, rightRow.Elements with
        | _, _ when leftRow.ElementKind <> rightRow.ElementKind ->
            raise (UnifyRowKindMismatch (leftRow.ElementKind, rightRow.ElementKind))
        | _, _ when leftRow.Scoped <> rightRow.Scoped ->
            raise (UnifyRowKindMismatch (leftRow.ElementKind, rightRow.ElementKind))
        | [], [] ->
            let ctor = if leftRow.Scoped then TEmptyRow else TEmptySet
            match leftRow.RowEnd, rightRow.RowEnd with
            | Some lv, Some rv -> Map.empty.Add(lv, typeVar rv ((rowKindCtor leftRow) leftRow.ElementKind))
            | Some lv, None -> Map.empty.Add(lv, ctor leftRow.ElementKind)
            | None, Some rv -> Map.empty.Add(rv, ctor leftRow.ElementKind)
            | None, None -> Map.empty
        | ls, [] ->
            match rightRow.RowEnd with
            | Some rv -> Map.empty.Add(rv, rowToType leftRow)
            | _ -> raise (UnifyRowRigidMismatch (rowToType leftRow, rowToType rightRow))
        | [], rs ->
            match leftRow.RowEnd with
            | Some lv -> Map.empty.Add(lv, rowToType rightRow)
            | _ -> raise (UnifyRowRigidMismatch (rowToType leftRow, rowToType rightRow))
        | ls, rs ->
            let overlapped = overlappingLabels (List.map rowElementHead ls) (List.map rowElementHead rs)
            if not (Set.isEmpty overlapped)
            then
                let label = Set.minElement overlapped
                if leftRow.Scoped
                then
                    // scoped rows only unify the first occurence of each label in the row, allowing multiple 'scoped' labels
                    let ((lElem, rElem), (lRest, rRest)) = decomposeMatchingLabel label leftRow rightRow
                    let fu = typeUnifyExn fresh lElem rElem
                    let ru = unifyRow fresh { leftRow with Elements = lRest } { rightRow with Elements = rRest }
                    composeSubstExn ru fu
                else
                    // non-scoped rows unify all occurences of each label in the row, and filter them out later in simplification
                    let elems, (lRest, rRest) = collectMatchingLabels label leftRow rightRow
                    let fUnis = Seq.pairwise elems |> Seq.map (fun (l,r) -> typeUnifyExn fresh l r)
                    let fu = Seq.fold (fun unif sub -> composeSubstExn unif sub) Map.empty fUnis
                    let ru = unifyRow fresh { leftRow with Elements = lRest } { rightRow with Elements = rRest }
                    composeSubstExn ru fu
            else
                let kindCtor = rowKindCtor leftRow
                match leftRow.RowEnd, rightRow.RowEnd with
                | Some lv, Some rv when lv = rv -> raise (UnifyRowRigidMismatch (rowToType leftRow, rowToType rightRow))
                | Some lv, Some rv ->
                    let freshVar = fresh.Fresh "r"
                    Map.empty
                        .Add(lv, typeSubstSimplifyExn (Map.empty.Add(rv, typeVar freshVar (kindCtor rightRow.ElementKind))) (rowToType rightRow))
                        .Add(rv, typeSubstSimplifyExn (Map.empty.Add(lv, typeVar freshVar (kindCtor leftRow.ElementKind))) (rowToType leftRow))
                | _ -> raise (UnifyRowRigidMismatch (rowToType leftRow, rowToType rightRow))

    let typeOverlap fresh l r =
        try
            typeUnifyExn fresh l r |> constant true
        with
            | _ -> false

    let solveAll fresh constraints =
        let rec solveConstraint cs subst =
            match cs with
            | [] -> subst
            | c :: cs ->
                printfn $"Unifying {c.Left} : {typeKindExn c.Left} = {c.Right} : {typeKindExn c.Right}"
                let unifier = typeUnifyExn fresh c.Left c.Right
                let replaced = List.map (constraintSubstExn unifier) cs
                solveConstraint replaced (composeSubstExn unifier subst)
        solveConstraint constraints Map.empty
    
    

    exception KindUnifyOccursException of Kind * Kind
    exception KindUnifyMismatchException of Kind * Kind

    let rec kindUnifyExn l r =
        match (l, r) with
        | _ when l = r -> Map.empty
        | KVar v, _ when Set.contains v (kindFree r) ->
            raise (KindUnifyOccursException (l, r))
        | _, KVar v when Set.contains v (kindFree l) ->
            raise (KindUnifyOccursException (l, r))
        | KVar v, _ -> Map.add v r Map.empty
        | _, KVar v -> Map.add v l Map.empty
        | KRow rl, KRow rr -> kindUnifyExn rl rr
        | KSeq sl, KSeq sr -> kindUnifyExn sl sr
        | KArrow (ll, lr), KArrow (rl, rr) ->
            let lu = kindUnifyExn ll rl
            let ru = kindUnifyExn (kindSubst lu lr) (kindSubst lu rr)
            composeKindSubst ru lu
        | _ -> raise (KindUnifyMismatchException (l, r))

    let solveKindConstraints constraints =
        let rec solveConstraint cs subst =
            match cs with
            | [] -> subst
            | c :: cs -> 
                printfn $"Unifying {c.LeftKind} = {c.RightKind}"
                let unifier = kindUnifyExn c.LeftKind c.RightKind
                solveConstraint (List.map (kindConstraintSubst unifier) cs) (composeKindSubst unifier subst)
        solveConstraint constraints Map.empty