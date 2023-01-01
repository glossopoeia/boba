namespace Boba.Core

module Unification =
    
    open Common
    open Fresh
    open Kinds
    open Types
    open Substitution

    type UnifyConstraint =
        | UCKindEq of Kind * Kind
        | UCTypeEqSyn of Type * Type
        | UCTypeEqBool of Boolean.Equation * Boolean.Equation * Kind
        | UCTypeEqFixed of Abelian.Equation<string, int> * Abelian.Equation<string, int>
        | UCTypeEqAbelian of Abelian.Equation<string, string> * Abelian.Equation<string, string> * Kind
        | UCTypeEqSeq of DotSeq.DotSeq<Type> * DotSeq.DotSeq<Type>
        | UCTypeEqRow of RowType * RowType
        override this.ToString() =
            match this with
            | UCKindEq (lk, rk) -> $"kind: {lk} ~~ {rk}"
            | UCTypeEqSyn (lt, rt) -> $"type: {lt} ~~ {rt}"
            | UCTypeEqBool (lb, rb, k) -> $"bool {k}: {lb} ~~ {rb}"
            | UCTypeEqFixed (lf, rf) -> $"fixed: {lf} ~~ {rf}"
            | UCTypeEqAbelian (la, ra, ak) -> $"abelian {ak}: {la} ~~ {ra}"
            | UCTypeEqSeq (ls, rs) -> $"seq: {TSeq (ls)} ~~ {TSeq (rs)}"
            | UCTypeEqRow (lr, rr) -> $"row: {lr} ~~ {rr}"
    
    let kindEqConstraint = curry UCKindEq
    let typeEqConstraint = curry UCTypeEqSyn
    let booleanEqConstraint l r k = UCTypeEqBool (l, r, k)
    let fixedEqConstraint = curry UCTypeEqFixed
    let abelianEqConstraint l r k = UCTypeEqAbelian (l, r, k)
    let sequenceEqConstraint = curry UCTypeEqSeq
    let rowEqConstraint = curry UCTypeEqRow

    let constraintFreeWithKinds cnstr =
        match cnstr with
        | UCKindEq _ -> Set.empty
        | UCTypeEqSyn (lt, rt) ->
            Set.union (typeFreeWithKinds lt) (typeFreeWithKinds rt)
        | UCTypeEqRow (lr, rr) ->
            Set.union (typeFreeWithKinds (rowToType lr)) (typeFreeWithKinds (rowToType rr))
        | UCTypeEqSeq (ls, rs) ->
            Set.union (typeFreeWithKinds (typeSeq ls)) (typeFreeWithKinds (typeSeq rs))
        | UCTypeEqBool (lb, rb, bk) ->
            Set.union
                (typeFreeWithKinds (booleanEqnToType bk lb))
                (typeFreeWithKinds (booleanEqnToType bk rb))
        | UCTypeEqAbelian (la, ra, ak) ->
            Set.union
                (typeFreeWithKinds (abelianEqnToType ak la))
                (typeFreeWithKinds (abelianEqnToType ak ra))
        | UCTypeEqFixed (lf, rf) ->
            Set.union (typeFreeWithKinds (fixedEqnToType lf)) (typeFreeWithKinds (fixedEqnToType rf))
    
    let constraintFree cnstr = constraintFreeWithKinds cnstr |> Set.map fst

    let rec constraintSubstExn fresh subst cnstr =
        match cnstr with
        | UCKindEq (lk, rk) -> kindEqConstraint (kindSubst subst lk) (kindSubst subst rk)
        | UCTypeEqSyn (lt, rt) ->
            typeEqConstraint (typeSubstExn fresh subst lt) (typeSubstExn fresh subst rt)
        | UCTypeEqRow (lr, rr) ->
            let (UCTypeEqSyn (lrs, rrs)) = constraintSubstExn fresh subst (typeEqConstraint (rowToType lr) (rowToType rr))
            rowEqConstraint (typeToRow lrs) (typeToRow rrs)
        | UCTypeEqSeq (ls, rs) ->
            let (UCTypeEqSyn (TSeq lss, TSeq rss)) =
                constraintSubstExn fresh subst (typeEqConstraint (typeSeq ls) (typeSeq rs))
            sequenceEqConstraint lss rss
        // NOTE: this is only valid as bool, fixed, and abelian are solved instantly
        // after being appended to the solve list, and thus are never in the 'to-be-solved'
        // section that has composed substitutions applied to it
        | UCTypeEqBool _ -> cnstr
        | UCTypeEqFixed _ -> cnstr
        | UCTypeEqAbelian _ -> cnstr

    exception UnifyKindOccursCheckFailure of Kind * Kind
    exception UnifyKindMismatchException of Kind * Kind
    exception MatchKindMismatch of Kind * Kind

    exception UnifyTypeKindMismatch of Type * Type * Kind * Kind
    exception UnifyRowKindMismatch of Kind * Kind
    exception UnifyAbelianMismatch of Type * Type
    exception UnifyBooleanMismatch of Type * Type
    exception UnifyTypeOccursCheckFailure of Type * Type
    exception UnifyRowRigidMismatch of Type * Type
    exception UnifyRigidRigidMismatch of Type * Type
    exception UnifySequenceMismatch of DotSeq.DotSeq<Type> * DotSeq.DotSeq<Type>

    exception MatchBooleanMismatch of Type * Type
    exception MatchAbelianMismatch of Type * Type
    exception MatchRowMismatch of Type * Type
    exception MatchStructuralMismatch of Type * Type
    exception MatchSequenceMismatch of DotSeq.DotSeq<Type> * DotSeq.DotSeq<Type>
    exception MatchNonValueSequence of Type * Type
    
    /// Utility method for when a unification step only breaks down the unification
    /// problem, and does not partially construct the result substitution.
    let constraintDecompose cnstrs = emptySubst, cnstrs

    /// Simple syntactic unification of kinds.
    let unifyKind lk rk =
        match lk, rk with
        | _ when kindEq lk rk ->
            constraintDecompose []
        | KVar v, _ when Set.contains v (kindFree rk) ->
            raise (UnifyKindOccursCheckFailure (lk, rk))
        | _, KVar v when Set.contains v (kindFree lk) ->
            raise (UnifyKindOccursCheckFailure (lk, rk))
        | KVar v, _ ->
            addKindSubst emptySubst v rk, []
        | _, KVar v ->
            addKindSubst emptySubst v lk, []
        | KRow rl, KRow rr ->
            constraintDecompose [kindEqConstraint rl rr]
        | KSeq sl, KSeq sr ->
            constraintDecompose [kindEqConstraint sl sr]
        | KArrow (ll, lr), KArrow (rl, rr) ->
            constraintDecompose [kindEqConstraint ll rl; kindEqConstraint lr rr]
        | _ ->
            raise (UnifyKindMismatchException (lk, rk))

    /// Simple syntactic unification of types, which checks to see if the given types should
    /// be unified via non-syntactic unification and generates those constraints instead
    /// as applicable.
    let unifyType lt rt =
        match lt, rt with
        | _ when lt = rt ->
            constraintDecompose []
        | (TAnd _ | TOr _ | TNot _), _ ->
            constraintDecompose [
                booleanEqConstraint
                    (typeToBooleanEqn (simplifyType lt))
                    (typeToBooleanEqn (simplifyType rt))
                    (typeKindExn lt)]
        | _, (TAnd _ | TOr _ | TNot _) ->
            constraintDecompose [
                booleanEqConstraint
                    (typeToBooleanEqn (simplifyType lt))
                    (typeToBooleanEqn (simplifyType rt))
                    (typeKindExn lt)]
        | _ when typeKindExn lt = primFixedKind || typeKindExn rt = primFixedKind ->
            constraintDecompose [
                fixedEqConstraint (typeToFixedEqn lt) (typeToFixedEqn rt);
                kindEqConstraint (typeKindExn lt) (typeKindExn rt)]
        | _ when isKindAbelian (typeKindExn lt) || isKindAbelian (typeKindExn rt) ->
            constraintDecompose [
                abelianEqConstraint (typeToUnitEqn lt) (typeToUnitEqn rt) (typeKindExn lt);
                kindEqConstraint (typeKindExn lt) (typeKindExn rt)]
        | _ when isKindExtensibleRow (typeKindExn lt) || isKindExtensibleRow (typeKindExn rt) ->
            constraintDecompose [rowEqConstraint (typeToRow lt) (typeToRow rt)]
        | TDotVar _, _ -> failwith "Dot vars should only occur in boolean types."
        | _, TDotVar _ -> failwith "Dot vars should only occur in boolean types."
        | TVar (nl, _), r when Set.contains nl (typeFree r) ->
            raise (UnifyTypeOccursCheckFailure (lt, r))
        | l, TVar (nr, _) when Set.contains nr (typeFree l) ->
            raise (UnifyTypeOccursCheckFailure (l, rt))
        | TVar (nl, k), r ->
            addTypeSubst emptySubst nl r, [kindEqConstraint k (typeKindExn r)]
        | l, TVar (nr, k) ->
            addTypeSubst emptySubst nr l, [kindEqConstraint k (typeKindExn l)]
        | TCon (ln, lk), TCon (rn, rk) when ln = rn ->
            constraintDecompose [kindEqConstraint lk rk]
        | TApp (ll, lr), TApp (rl, rr) ->
            constraintDecompose [typeEqConstraint ll rl; typeEqConstraint lr rr]
        | TSeq ls, TSeq rs ->
            constraintDecompose [kindEqConstraint (typeKindExn lt) (typeKindExn rt); sequenceEqConstraint ls rs]
        | _ ->
            raise (UnifyRigidRigidMismatch (lt, rt))
    
    let unifyBoolean lb rb kind =
        //printfn $"Sub-unifying {lb} ~ {rb}"
        match Boolean.unify lb rb with
        | Some subst ->
            //printfn $"Resulting sub-unifier:"
            //Map.iter (fun k v -> printfn $"{k} -> {v}") subst
            typeSubst (mapValues (booleanEqnToType kind) subst), []
        | None -> raise (UnifyBooleanMismatch (booleanEqnToType kind lb, booleanEqnToType kind rb))
    
    let unifyFixed fresh lf rf =
        match Abelian.unify fresh lf rf with
        | Some subst -> typeSubst (mapValues fixedEqnToType subst), []
        | None -> raise (UnifyAbelianMismatch (fixedEqnToType lf, fixedEqnToType rf))
    
    let unifyAbelian fresh la ra ak =
        match Abelian.unify fresh la ra with
        | Some subst -> typeSubst (mapValues (abelianEqnToType ak) subst), []
        | None -> raise (UnifyAbelianMismatch (abelianEqnToType ak la, abelianEqnToType ak ra))
    
    /// Convenience method used to help expand pattern types at the end of sequences with fresh
    /// type variables that all map back to one sequence variable.
    let rec genSplitSub (fresh: FreshVars) vars =
        match vars with
        | [] -> Map.empty
        | (x, k) :: xs ->
            let freshInd = fresh.Fresh x
            let freshSeq = fresh.Fresh x
            let sub = genSplitSub fresh xs
            Map.add x (typeSeq (DotSeq.SInd (typeVar freshInd k, (DotSeq.SDot (typeVar freshSeq k, DotSeq.SEnd))))) sub

    /// Sequence unification is similar to row unification, with two major differences. The first
    /// is that sequence unification is ordered, so non-variable arity elements at the same index
    /// in a sequence must unify, regardless of any 'labels'. The second is that a sequence need
    /// not be terminated by a simple sequence variable; we can instead terminate with a sequence
    /// pattern type, which allows for more interesting types in things like variable arity tuples.
    /// An example is ((a,b)...), a sequence pattern type with two variables, representing a tuple
    /// of two-tuples that is arbitrarily long. This function handles unifying that type with something
    /// liek ((Int,Bool),(String,List a)...) for example.
    let unifySequence fresh ls rs =
        match ls, rs with
        | DotSeq.SEnd, DotSeq.SEnd ->
            constraintDecompose []
        | DotSeq.SInd (li, lss), DotSeq.SInd (ri, rss) ->
            constraintDecompose [typeEqConstraint li ri; sequenceEqConstraint lss rss]
        | DotSeq.SDot (ld, DotSeq.SEnd), DotSeq.SDot (rd, DotSeq.SEnd) ->
            constraintDecompose [typeEqConstraint ld rd]
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SEnd ->
            typeSubst ([for (v, k) in List.ofSeq (typeFreeWithKinds li) do (v, typeSeq DotSeq.SEnd)] |> Map.ofList), []
        | DotSeq.SEnd, DotSeq.SDot (ri, DotSeq.SEnd) ->
            typeSubst ([for (v, k) in List.ofSeq (typeFreeWithKinds ri) do (v, typeSeq DotSeq.SEnd)] |> Map.ofList), []
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SInd _ when not (Set.isEmpty (Set.intersect (typeFree li) (typeFree (TSeq (rs))))) ->
            raise (UnifyTypeOccursCheckFailure (TSeq (ls), TSeq (rs)))
        | DotSeq.SInd _, DotSeq.SDot (ri, DotSeq.SEnd) when not (Set.isEmpty (Set.intersect (typeFree ri) (typeFree (TSeq (ls))))) ->
            raise (UnifyTypeOccursCheckFailure (TSeq (ls), TSeq (rs)))
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SInd (ri, rs) ->
            let freshVars = typeSubst (typeFreeWithKinds li |> List.ofSeq |> genSplitSub fresh)
            freshVars,
            [typeEqConstraint
                (typeSubstSimplifyExn fresh freshVars (typeSeq (DotSeq.dot li DotSeq.SEnd)))
                (typeSeq (DotSeq.ind ri rs))]
        | DotSeq.SInd (li, ls), DotSeq.SDot (ri, DotSeq.SEnd) ->
            let freshVars = typeSubst (typeFreeWithKinds ri |> List.ofSeq |> genSplitSub fresh)
            freshVars,
            [typeEqConstraint
                (typeSubstSimplifyExn fresh freshVars (typeSeq (DotSeq.dot ri DotSeq.SEnd)))
                (typeSeq (DotSeq.ind li ls))]
        | _ ->
            raise (UnifySequenceMismatch (ls, rs))
    
    /// Convenience function for getting the shared set of labels in two lists
    let overlappingLabels left right = Set.intersect (Set.ofList left) (Set.ofList right)

    /// Find the first matching labeled element in the elements of each given row, extract it,
    /// and remove it from the elements of each row.
    let decomposeMatchingLabel label leftRow rightRow =
        let rec decomposeOnLabel acc fs =
            match fs with
            | f :: fs when rowElementHead f = label -> (f, List.append acc fs)
            | f :: fs -> decomposeOnLabel (f :: acc) fs
            | [] -> failwith $"Internal error: expected to find field {label} in row"
        let lMatched, lRest = decomposeOnLabel [] leftRow.Elements
        let rMatched, rRest = decomposeOnLabel [] rightRow.Elements
        (lMatched, rMatched), (lRest, rRest)

    /// Solves a row constraint, breaking down the constraint if multiple row labels are present.
    /// Row unification is 'scoped orderless' per Daan Leijen's scoped labels technique.
    let unifyRow (fresh: FreshVars) leftRow rightRow =
        match leftRow.Elements, rightRow.Elements with
        | _, _ when leftRow.ElementKind <> rightRow.ElementKind ->
            raise (UnifyRowKindMismatch (leftRow.ElementKind, rightRow.ElementKind))
        | [], [] ->
            // since we support polymorphic row kinds, we need to make sure these rows have the same kind
            // eventually, so we add a constraint when we reach the end of a row
            match leftRow.RowEnd, rightRow.RowEnd with
            | Some lv, Some rv ->
                addTypeSubst emptySubst lv (typeVar rv (KRow leftRow.ElementKind)),
                [kindEqConstraint leftRow.ElementKind rightRow.ElementKind]
            | Some lv, None ->
                addTypeSubst emptySubst lv (TEmptyRow leftRow.ElementKind),
                [kindEqConstraint leftRow.ElementKind rightRow.ElementKind]
            | None, Some rv ->
                addTypeSubst emptySubst rv (TEmptyRow leftRow.ElementKind),
                [kindEqConstraint leftRow.ElementKind rightRow.ElementKind]
            | None, None ->
                constraintDecompose [kindEqConstraint leftRow.ElementKind rightRow.ElementKind]
        | ls, [] ->
            match rightRow.RowEnd with
            | Some rv ->
                addTypeSubst emptySubst rv (rowToType leftRow),
                [kindEqConstraint leftRow.ElementKind rightRow.ElementKind]
            | _ -> raise (UnifyRowRigidMismatch (rowToType leftRow, rowToType rightRow))
        | [], rs ->
            match leftRow.RowEnd with
            | Some lv ->
                addTypeSubst emptySubst lv (rowToType rightRow),
                [kindEqConstraint leftRow.ElementKind rightRow.ElementKind]
            | _ -> raise (UnifyRowRigidMismatch (rowToType leftRow, rowToType rightRow))
        | ls, rs ->
            let overlapped = overlappingLabels (List.map rowElementHead ls) (List.map rowElementHead rs)
            if not (Set.isEmpty overlapped)
            then
                // we have overlapping labels, so we must make sure their arguments unify
                // we adjust the rest of the rows so that the matched labels are moved up front
                // this means the resulting lists are smaller, which guarantees termination
                let label = Set.minElement overlapped
                let (lElem, rElem), (lRest, rRest) = decomposeMatchingLabel label leftRow rightRow
                constraintDecompose [
                    typeEqConstraint lElem rElem;
                    rowEqConstraint { leftRow with Elements = lRest } { rightRow with Elements = rRest }]
            else
                // no overlapping labels, which means the rows can be concatenated with a new row
                // variable at the end, but only if the row variables are not the same. In the
                // latter case we know the rows cannot possibly unify
                match leftRow.RowEnd, rightRow.RowEnd with
                | Some lv, Some rv when lv = rv ->
                    raise (UnifyRowRigidMismatch (rowToType leftRow, rowToType rightRow))
                | Some lv, Some rv ->
                    let freshVar = fresh.Fresh "r"
                    let rvSub =
                        typeSubstSimplifyExn fresh
                            (addTypeSubst emptySubst lv (typeVar freshVar (KRow leftRow.ElementKind)))
                            (rowToType leftRow)
                    let lvSub =
                        typeSubstSimplifyExn fresh
                            (addTypeSubst emptySubst rv (typeVar freshVar (KRow rightRow.ElementKind)))
                            (rowToType rightRow)
                    addTypeSubst (addTypeSubst emptySubst rv rvSub) lv lvSub,
                    [kindEqConstraint leftRow.ElementKind rightRow.ElementKind]
                | _ -> raise (UnifyRowRigidMismatch (rowToType leftRow, rowToType rightRow))
    
    /// Simple syntactic matching on kinds.
    let matchKind lk rk =
        match lk, rk with
        | _ when kindEq lk rk ->
            constraintDecompose []
        | KVar v, _ ->
            addKindSubst emptySubst v rk, []
        | KRow rl, KRow rr ->
            constraintDecompose [kindEqConstraint rl rr]
        | KSeq sl, KSeq sr ->
            constraintDecompose [kindEqConstraint sl sr]
        | KArrow (ll, lr), KArrow (rl, rr) ->
            constraintDecompose [kindEqConstraint ll rl; kindEqConstraint lr rr]
        | _ ->
            raise (MatchKindMismatch (lk, rk))

    /// Simple syntactic matching of types, which checks to see if the given types should
    /// be matched via non-syntactic matching and generates those constraints instead
    /// as applicable.
    let matchType strict lt rt =
        match lt, rt with
        | _ when lt = rt ->
            constraintDecompose []
        | (TAnd _ | TOr _ | TNot _), _ ->
            constraintDecompose [
                booleanEqConstraint
                    (typeToBooleanEqn (simplifyType lt))
                    (typeToBooleanEqn (simplifyType rt))
                    (typeKindExn lt)]
        | _, (TAnd _ | TOr _ | TNot _) ->
            constraintDecompose [
                booleanEqConstraint
                    (typeToBooleanEqn (simplifyType lt))
                    (typeToBooleanEqn (simplifyType rt))
                    (typeKindExn lt)]
        | TDotVar (nl, k), r ->
            addTypeSubst emptySubst nl r, [kindEqConstraint k (typeKindExn r)]
        | TVar (nl, k), (TVar (_, rk)) ->
            addTypeSubst emptySubst nl rt, [kindEqConstraint k rk]
        | TVar (_, k), r when strict && isKindExtensibleRow k ->
            raise (MatchRowMismatch (lt, r))
        | TVar (nl, k), r ->
            addTypeSubst emptySubst nl r, [kindEqConstraint k (typeKindExn r)]
        | _ when typeKindExn lt = primFixedKind || typeKindExn rt = primFixedKind ->
            constraintDecompose [
                fixedEqConstraint (typeToFixedEqn lt) (typeToFixedEqn rt);
                kindEqConstraint (typeKindExn lt) (typeKindExn rt)]
        | _ when isKindAbelian (typeKindExn lt) || isKindAbelian (typeKindExn rt) ->
            constraintDecompose [
                abelianEqConstraint (typeToUnitEqn lt) (typeToUnitEqn rt) (typeKindExn lt);
                kindEqConstraint (typeKindExn lt) (typeKindExn rt)]
        | _ when isKindExtensibleRow (typeKindExn lt) || isKindExtensibleRow (typeKindExn rt) ->
            constraintDecompose [rowEqConstraint (typeToRow lt) (typeToRow rt)]
        | TCon (ln, lk), TCon (rn, rk) when ln = rn ->
            constraintDecompose [kindEqConstraint lk rk]
        | TApp (ll, lr), TApp (rl, rr) ->
            constraintDecompose [typeEqConstraint ll rl; typeEqConstraint lr rr]
        | TSeq ls, TSeq rs ->
            constraintDecompose [kindEqConstraint (typeKindExn lt) (typeKindExn rt); sequenceEqConstraint ls rs]
        | _ ->
            raise (MatchStructuralMismatch (lt, rt))
    
    let matchBoolean lb rb kind =
        if lb = rb then emptySubst, []
        else
        match Boolean.unify lb (Boolean.rigidify rb) with
        | Some subst -> typeSubst (mapValues (booleanEqnToType kind) subst), []
        | None -> raise (MatchBooleanMismatch (booleanEqnToType kind lb, booleanEqnToType kind rb))
    
    let matchFixed fresh lf rf =
        match Abelian.matchEqns fresh lf rf with
        | Some subst -> typeSubst (mapValues fixedEqnToType subst), []
        | None -> raise (MatchAbelianMismatch (fixedEqnToType lf, fixedEqnToType rf))
    
    let matchAbelian fresh la ra kind =
        match Abelian.matchEqns fresh la ra with
        | Some subst -> typeSubst (mapValues (abelianEqnToType kind) subst), []
        | None -> raise (MatchAbelianMismatch (abelianEqnToType kind la, abelianEqnToType kind ra))
    
    let matchSequence fresh ls rs =
        match ls, rs with
        | DotSeq.SEnd, DotSeq.SEnd ->
            constraintDecompose []
        | DotSeq.SInd (li, lss), DotSeq.SInd (ri, rss) ->
            constraintDecompose [typeEqConstraint li ri; sequenceEqConstraint lss rss]
        | DotSeq.SDot (ld, DotSeq.SEnd), DotSeq.SDot (rd, DotSeq.SEnd) ->
            constraintDecompose [typeEqConstraint ld rd]
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SEnd ->
            typeSubst ([for (v, k) in List.ofSeq (typeFreeWithKinds li) do (v, typeSeq DotSeq.SEnd)] |> Map.ofList), []
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SInd (ri, rss) ->
            let freshVars = typeSubst (typeFreeWithKinds li |> List.ofSeq |> genSplitSub fresh)
            freshVars,
            [typeEqConstraint
                (typeSubstSimplifyExn fresh freshVars (typeSeq (DotSeq.dot li DotSeq.SEnd)))
                (typeSeq (DotSeq.ind ri rss))]
        | _ ->
            raise (MatchSequenceMismatch (ls, rs))
    
    let strictMatchSequence fresh ls rs =
        match ls, rs with
        | DotSeq.SEnd, DotSeq.SEnd ->
            constraintDecompose []
        | DotSeq.SInd (li, lss), DotSeq.SInd (ri, rss) ->
            constraintDecompose [typeEqConstraint li ri; sequenceEqConstraint lss rss]
        | DotSeq.SDot (ld, DotSeq.SEnd), DotSeq.SDot (rd, DotSeq.SEnd) ->
            constraintDecompose [typeEqConstraint ld rd]
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SEnd ->
            typeSubst ([for (v, k) in List.ofSeq (typeFreeWithKinds li) do (v, typeSeq DotSeq.SEnd)] |> Map.ofList), []
        | _ ->
            raise (MatchSequenceMismatch (ls, rs))
    
    let matchRow (fresh: FreshVars) strict leftRow rightRow =
        match leftRow.Elements, rightRow.Elements with
        | _, _ when not (kindEq leftRow.ElementKind rightRow.ElementKind) ->
            raise (UnifyRowKindMismatch (leftRow.ElementKind, rightRow.ElementKind))
        | [], [] ->
            // since we support polymorphic row kinds, we need to make sure these rows have the same kind
            // eventually, so we add a constraint when we reach the end of a row
            match leftRow.RowEnd, rightRow.RowEnd with
            | Some lv, Some rv ->
                addTypeSubst emptySubst lv (typeVar rv (KRow leftRow.ElementKind)),
                [kindEqConstraint leftRow.ElementKind rightRow.ElementKind]
            | Some lv, None ->
                addTypeSubst emptySubst lv (TEmptyRow leftRow.ElementKind),
                [kindEqConstraint leftRow.ElementKind rightRow.ElementKind]
            | None, Some rv ->
                raise (MatchRowMismatch (rowToType leftRow, rowToType rightRow))
            | None, None ->
                constraintDecompose [kindEqConstraint leftRow.ElementKind rightRow.ElementKind]
        | ls, [] ->
            raise (MatchRowMismatch (rowToType leftRow, rowToType rightRow))
        | [], rs ->
            match leftRow.RowEnd with
            | Some lv ->
                if strict
                then raise (MatchRowMismatch (rowToType leftRow, rowToType rightRow))
                else
                    addTypeSubst emptySubst lv (rowToType rightRow),
                    [kindEqConstraint leftRow.ElementKind rightRow.ElementKind]
            | _ -> raise (MatchRowMismatch (rowToType leftRow, rowToType rightRow))
        | ls, rs ->
            let overlapped = overlappingLabels (List.map rowElementHead ls) (List.map rowElementHead rs)
            if not (Set.isEmpty overlapped)
            then
                // we have overlapping labels, so we must make sure their arguments unify
                // we adjust the rest of the rows so that the matched labels are moved up front
                // this means the resulting lists are smaller, which guarantees termination
                let label = Set.minElement overlapped
                let (lElem, rElem), (lRest, rRest) = decomposeMatchingLabel label leftRow rightRow
                constraintDecompose [
                    typeEqConstraint lElem rElem;
                    rowEqConstraint { leftRow with Elements = lRest } { rightRow with Elements = rRest }]
            else raise (MatchRowMismatch (rowToType leftRow, rowToType rightRow))

    /// Partially solve a single constraint, returning a substitution that partially unifies the constraint,
    /// and any more steps that need to be taken to fully solve the constraint.
    let solveUnifyStep fresh uc =
        match uc with
        | UCKindEq (lk, rk) -> unifyKind lk rk
        | UCTypeEqSyn (lt, rt) -> unifyType lt rt
        | UCTypeEqBool (lb, rb, bk) -> unifyBoolean lb rb bk
        | UCTypeEqFixed (lf, rf) -> unifyFixed fresh lf rf
        | UCTypeEqAbelian (la, ra, ak) -> unifyAbelian fresh la ra ak
        | UCTypeEqSeq (ls, rs) -> unifySequence fresh ls rs
        | UCTypeEqRow (lr, rr) -> unifyRow fresh lr rr
    
    let solveMatchStep fresh strict uc =
        match uc with
        | UCKindEq (lk, rk) -> matchKind lk rk
        | UCTypeEqSyn (lt, rt) -> matchType strict lt rt
        | UCTypeEqBool (lb, rb, bk) -> matchBoolean lb rb bk
        | UCTypeEqFixed (lf, rf) -> matchFixed fresh lf rf
        | UCTypeEqAbelian (la, ra, ak) -> matchAbelian fresh la ra ak
        | UCTypeEqSeq (ls, rs) ->
            if strict
            then strictMatchSequence fresh ls rs
            else matchSequence fresh ls rs
        | UCTypeEqRow (lr, rr) -> matchRow fresh strict lr rr
    
    /// Solve the given list of constraints from front to back. Returns the substitution
    /// that represents the most general unifier for all the constraints.
    let solveComposeAll fresh constraints =
        let rec solveConstraint cs subst =
            match cs with
            | [] -> subst
            | c :: cs ->
                //printfn $"Unifying {c}"
                let unifier, decomposed = solveUnifyStep fresh c
                let composeUnifier = composeSubstExn fresh unifier subst
                let replaced = List.map (constraintSubstExn fresh composeUnifier) (List.append decomposed cs)
                solveConstraint replaced composeUnifier
        solveConstraint constraints emptySubst
    
    let solveMergeAll fresh strict constraints =
        let rec solveConstraint cs subst =
            match cs with
            | [] -> subst
            | c :: cs ->
                //printfn $"Matching {c}"
                let matcher, decomposed = solveMatchStep fresh strict c
                let mergeMatcher = mergeSubstExn fresh matcher subst
                let replaced = List.map (constraintSubstExn fresh mergeMatcher) (List.append decomposed cs)
                solveConstraint replaced mergeMatcher
        solveConstraint constraints emptySubst
    
    /// Compute the substitution that represents the most general unifier for the two given types.
    /// The resulting substitution may contain mappings from kind variables to kinds if there were
    /// any kind variables in either supplied type.
    let typeUnifyExn fresh l r =
        solveComposeAll fresh [typeEqConstraint l r]
    
    /// Return whether two types can unify.
    let typeOverlap fresh l r =
        try
            typeUnifyExn fresh l r |> constant true
        with
            | _ -> false
    
    /// Compute the substitution that represents the most general unifier for the two given kinds.
    let kindUnifyExn fresh l r =
        solveComposeAll fresh [kindEqConstraint l r]
    
    /// Generate a substitution `s` such that `s(l) = r`, where equality is according to the
    /// equational theory of each subterm (i.e. not necessarily syntactically equal, but always
    /// semantically equal).
    let typeMatchExn fresh l r =
        solveMergeAll fresh false [typeEqConstraint l r]
    
    /// Generate a substitution `s` such that `s(l) = r`, when applied to kinds.
    let kindMatchExn fresh l r =
        solveMergeAll fresh false [kindEqConstraint l r]
    
    /// Generate a substitution `s` such that `s(l) = r`, where equality is according to the
    /// equational theory of each subterm (i.e. not necessarily syntactically equal, but always
    /// semantically equal). The strictness here is that sequence variables are not expanded,
    /// i.e. they are essentially treated as individual variables.
    let strictTypeMatchExn fresh l r =
        solveMergeAll fresh true [typeEqConstraint l r]
    
    /// Returns true if the `l` type is more general than (or at least as general as)
    /// the given type for `r`.
    let isTypeMatch fresh l r =
        try
            typeMatchExn fresh l r |> constant true
        with
            | ex -> false
    
    /// Returns true if the `l` type is more general than (or at least as general as)
    /// the given type for `r`, without expanding sequence or row variables.
    let isStrictTypeMatch fresh l r =
        try
            strictTypeMatchExn fresh l r |> constant true
        with
            | ex -> false
    
    let isKindMatch fresh l r =
        try
            kindMatchExn fresh l r |> constant true
        with
            | ex -> false