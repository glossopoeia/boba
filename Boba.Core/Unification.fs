namespace Boba.Core

module Unification =
    
    open Common
    open Fresh
    open Kinds
    open Types

    type UnifyConstraint =
        | UCKind of Kind * Kind
        | UCTypeSyn of Type * Type
        | UCTypeBool of Boolean.Equation * Boolean.Equation * Kind
        | UCTypeFixed of Abelian.Equation<string, int> * Abelian.Equation<string, int>
        | UCTypeAbelian of Abelian.Equation<string, string> * Abelian.Equation<string, string> * Kind
        | UCTypeSeq of DotSeq.DotSeq<Type> * DotSeq.DotSeq<Type>
        | UCTypeRow of RowType * RowType
        override this.ToString() =
            match this with
            | UCKind (lk, rk) -> $"kind: {lk} ~~ {rk}"
            | UCTypeSyn (lt, rt) -> $"type: {lt} ~~ {rt}"
            | UCTypeBool (lb, rb, k) -> $"bool {k}: {lb} ~~ {rb}"
            | UCTypeFixed (lf, rf) -> $"fixed: {lf} ~~ {rf}"
            | UCTypeAbelian (la, ra, ak) -> $"abelian {ak}: {la} ~~ {ra}"
            | UCTypeSeq (ls, rs) -> $"seq: {TSeq (ls, primValueKind)} ~~ {TSeq (rs, primValueKind)}"
            | UCTypeRow (lr, rr) -> $"row: {lr} ~~ {rr}"
    
    let kindEqConstraint = curry UCKind
    let typeEqConstraint = curry UCTypeSyn
    let booleanEqConstraint l r k = UCTypeBool (l, r, k)
    let fixedEqConstraint = curry UCTypeFixed
    let abelianEqConstraint l r k = UCTypeAbelian (l, r, k)
    let sequenceEqConstraint = curry UCTypeSeq
    let rowEqConstraint = curry UCTypeRow

    let constraintFreeWithKinds cnstr =
        match cnstr with
        | UCKind _ -> Set.empty
        | UCTypeSyn (lt, rt) ->
            Set.union (typeFreeWithKinds lt) (typeFreeWithKinds rt)
        | UCTypeRow (lr, rr) ->
            Set.union (typeFreeWithKinds (rowToType lr)) (typeFreeWithKinds (rowToType rr))
        | UCTypeSeq (ls, rs) ->
            Set.union (typeFreeWithKinds (typeValueSeq ls)) (typeFreeWithKinds (typeValueSeq rs))
        | UCTypeBool (lb, rb, bk) ->
            Set.union
                (typeFreeWithKinds (booleanEqnToType bk lb))
                (typeFreeWithKinds (booleanEqnToType bk rb))
        | UCTypeAbelian (la, ra, ak) ->
            Set.union
                (typeFreeWithKinds (abelianEqnToType ak la))
                (typeFreeWithKinds (abelianEqnToType ak ra))
        | UCTypeFixed (lf, rf) ->
            Set.union (typeFreeWithKinds (fixedEqnToType lf)) (typeFreeWithKinds (fixedEqnToType rf))
    
    let constraintFree cnstr = constraintFreeWithKinds cnstr |> Set.map fst

    let rec constraintSubstExn fresh kSubst tSubst cnstr =
        match cnstr with
        | UCKind (lk, rk) -> kindEqConstraint (kindSubst kSubst lk) (kindSubst kSubst rk)
        | UCTypeSyn (lt, rt) ->
            let ltk, rtk = typeKindSubstExn kSubst lt, typeKindSubstExn kSubst rt
            typeEqConstraint (typeSubstExn fresh tSubst ltk) (typeSubstExn fresh tSubst rtk)
        | UCTypeRow (lr, rr) ->
            let (UCTypeSyn (lrs, rrs)) = constraintSubstExn fresh kSubst tSubst (typeEqConstraint (rowToType lr) (rowToType rr))
            rowEqConstraint (typeToRow lrs) (typeToRow rrs)
        | UCTypeSeq (ls, rs) ->
            let (UCTypeSyn (TSeq (lss, _), TSeq (rss, _))) =
                constraintSubstExn fresh kSubst tSubst (typeEqConstraint (TSeq (ls, primValueKind)) (TSeq (rs, primValueKind)))
            sequenceEqConstraint lss rss
        // NOTE: this is only valid as bool, fixed, and abelian are solved instantly
        // after being appended to the solve list, and thus are never in the 'to-be-solved'
        // section that has composed substitutions applied to it
        | UCTypeBool _ -> cnstr
        | UCTypeFixed _ -> cnstr
        | UCTypeAbelian _ -> cnstr

    exception UnifyKindOccursCheckFailure of Kind * Kind
    exception UnifyKindMismatchException of Kind * Kind

    exception UnifyTypeKindMismatch of Type * Type * Kind * Kind
    exception UnifyRowKindMismatch of Kind * Kind
    exception UnifyAbelianMismatch of Type * Type
    exception UnifyBooleanMismatch of Type * Type
    exception UnifyTypeOccursCheckFailure of Type * Type
    exception UnifyRowRigidMismatch of Type * Type
    exception UnifyRigidRigidMismatch of Type * Type
    exception UnifySequenceMismatch of DotSeq.DotSeq<Type> * DotSeq.DotSeq<Type>
    exception UnifyNonValueSequence of Type * Type
    
    /// Utility method for when a unification step only breaks down the unification
    /// problem, and does not partially construct the result substitution.
    let unifyDecompose cnstrs = Map.empty, Map.empty, cnstrs

    /// Simple syntactic unification of kinds.
    let unifyKind lk rk =
        match lk, rk with
        | _ when lk = rk ->
            unifyDecompose []
        | KVar v, _ when Set.contains v (kindFree rk) ->
            raise (UnifyKindOccursCheckFailure (lk, rk))
        | _, KVar v when Set.contains v (kindFree lk) ->
            raise (UnifyKindOccursCheckFailure (lk, rk))
        | KVar v, _ ->
            Map.empty, Map.add v rk Map.empty, []
        | _, KVar v ->
            Map.empty, Map.add v lk Map.empty, []
        | KRow rl, KRow rr ->
            unifyDecompose [kindEqConstraint rl rr]
        | KSeq sl, KSeq sr ->
            unifyDecompose [kindEqConstraint sl sr]
        | KArrow (ll, lr), KArrow (rl, rr) ->
            unifyDecompose [kindEqConstraint ll rl; kindEqConstraint lr rr]
        | _ ->
            raise (UnifyKindMismatchException (lk, rk))

    /// Simple syntactic unification of types, which checks to see if the given types should
    /// be unified via non-syntactic unification and generates those constraints instead
    /// as applicable.
    let unifyType lt rt =
        match lt, rt with
        | _ when lt = rt ->
            unifyDecompose []
        | (TAnd _ | TOr _ | TNot _), _ ->
            unifyDecompose [
                booleanEqConstraint
                    (typeToBooleanEqn (simplifyType lt))
                    (typeToBooleanEqn (simplifyType rt))
                    (typeKindExn lt)]
        | _, (TAnd _ | TOr _ | TNot _) ->
            unifyDecompose [
                booleanEqConstraint
                    (typeToBooleanEqn (simplifyType lt))
                    (typeToBooleanEqn (simplifyType rt))
                    (typeKindExn lt)]
        | _ when typeKindExn lt = primFixedKind || typeKindExn rt = primFixedKind ->
            unifyDecompose [
                fixedEqConstraint (typeToFixedEqn lt) (typeToFixedEqn rt);
                kindEqConstraint (typeKindExn lt) (typeKindExn rt)]
        | _ when isKindAbelian (typeKindExn lt) || isKindAbelian (typeKindExn rt) ->
            unifyDecompose [
                abelianEqConstraint (typeToUnitEqn lt) (typeToUnitEqn rt) (typeKindExn lt);
                kindEqConstraint (typeKindExn lt) (typeKindExn rt)]
        | _ when isKindExtensibleRow (typeKindExn lt) || isKindExtensibleRow (typeKindExn rt) ->
            unifyDecompose [rowEqConstraint (typeToRow lt) (typeToRow rt)]
        | TDotVar _, _ -> failwith "Dot vars should only occur in boolean types."
        | _, TDotVar _ -> failwith "Dot vars should only occur in boolean types."
        | TVar (nl, _), r when Set.contains nl (typeFree r) ->
            raise (UnifyTypeOccursCheckFailure (lt, r))
        | l, TVar (nr, _) when Set.contains nr (typeFree l) ->
            raise (UnifyTypeOccursCheckFailure (l, rt))
        | TVar (nl, k), r ->
            Map.add nl r Map.empty, Map.empty, [kindEqConstraint k (typeKindExn r)]
        | l, TVar (nr, k) ->
            Map.add nr l Map.empty, Map.empty, [kindEqConstraint k (typeKindExn l)]
        //| _ when typeKindExn lt <> typeKindExn rt ->
        //    raise (UnifyTypeKindMismatch (lt, rt, typeKindExn lt, typeKindExn rt))
        | TApp (ll, lr), TApp (rl, rr) ->
            unifyDecompose [typeEqConstraint ll rl; typeEqConstraint lr rr]
        | TSeq (ls, lk), TSeq (rs, rk) when lk = rk && lk = primValueKind ->
            unifyDecompose [sequenceEqConstraint ls rs]
        | TSeq _, TSeq _ ->
            raise (UnifyNonValueSequence (lt, rt))
        | _ ->
            raise (UnifyRigidRigidMismatch (lt, rt))
    
    let unifyBoolean lb rb kind =
        //printfn $"Sub-unifying {lb} ~ {rb}"
        match Boolean.unify lb rb with
        | Some subst ->
            //printfn $"Resulting sub-unifier:"
            //Map.iter (fun k v -> printfn $"{k} -> {v}") subst
            mapValues (booleanEqnToType kind) subst, Map.empty, []
        | None -> raise (UnifyBooleanMismatch (booleanEqnToType kind lb, booleanEqnToType kind rb))
    
    let unifyFixed fresh lf rf =
        match Abelian.unify fresh lf rf with
        | Some subst -> mapValues fixedEqnToType subst, Map.empty, []
        | None -> raise (UnifyAbelianMismatch (fixedEqnToType lf, fixedEqnToType rf))
    
    let unifyAbelian fresh la ra ak =
        match Abelian.unify fresh la ra with
        | Some subst -> mapValues (abelianEqnToType ak) subst, Map.empty, []
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
            Map.add x (TSeq (DotSeq.SInd (typeVar freshInd k, (DotSeq.SDot (typeVar freshSeq k, DotSeq.SEnd))), k)) sub

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
            Map.empty, Map.empty, []
        | DotSeq.SInd (li, lss), DotSeq.SInd (ri, rss) ->
            unifyDecompose [typeEqConstraint li ri; sequenceEqConstraint lss rss]
        | DotSeq.SDot (ld, DotSeq.SEnd), DotSeq.SDot (rd, DotSeq.SEnd) ->
            unifyDecompose [typeEqConstraint ld rd]
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SEnd ->
            [for (v, k) in List.ofSeq (typeFreeWithKinds li) do (v, TSeq (DotSeq.SEnd, k))] |> Map.ofList, Map.empty, []
        | DotSeq.SEnd, DotSeq.SDot (ri, DotSeq.SEnd) ->
            [for (v, k) in List.ofSeq (typeFreeWithKinds ri) do (v, TSeq (DotSeq.SEnd, k))] |> Map.ofList, Map.empty, []
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SInd _ when not (Set.isEmpty (Set.intersect (typeFree li) (typeFree (TSeq (rs, primValueKind))))) ->
            raise (UnifyTypeOccursCheckFailure (TSeq (ls, primValueKind), TSeq (rs, primValueKind)))
        | DotSeq.SInd _, DotSeq.SDot (ri, DotSeq.SEnd) when not (Set.isEmpty (Set.intersect (typeFree ri) (typeFree (TSeq (ls, primValueKind))))) ->
            raise (UnifyTypeOccursCheckFailure (TSeq (ls, primValueKind), TSeq (rs, primValueKind)))
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SInd (ri, rs) ->
            let freshVars = typeFreeWithKinds li |> List.ofSeq |> genSplitSub fresh
            freshVars,
            Map.empty,
            [typeEqConstraint
                (typeSubstSimplifyExn fresh freshVars (TSeq (DotSeq.dot li DotSeq.SEnd, primValueKind)))
                (TSeq (DotSeq.ind ri rs, primValueKind))]
        | DotSeq.SInd (li, ls), DotSeq.SDot (ri, DotSeq.SEnd) ->
            let freshVars = typeFreeWithKinds ri |> List.ofSeq |> genSplitSub fresh
            freshVars,
            Map.empty,
            [typeEqConstraint
                (typeSubstSimplifyExn fresh freshVars (TSeq (DotSeq.dot ri DotSeq.SEnd, primValueKind)))
                (TSeq (DotSeq.ind li ls, primValueKind))]
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
                Map.empty.Add(lv, typeVar rv (KRow leftRow.ElementKind)),
                Map.empty,
                [kindEqConstraint leftRow.ElementKind rightRow.ElementKind]
            | Some lv, None ->
                Map.empty.Add(lv, TEmptyRow leftRow.ElementKind),
                Map.empty,
                [kindEqConstraint leftRow.ElementKind rightRow.ElementKind]
            | None, Some rv ->
                Map.empty.Add(rv, TEmptyRow leftRow.ElementKind),
                Map.empty,
                [kindEqConstraint leftRow.ElementKind rightRow.ElementKind]
            | None, None ->
                unifyDecompose [kindEqConstraint leftRow.ElementKind rightRow.ElementKind]
        | ls, [] ->
            match rightRow.RowEnd with
            | Some rv ->
                Map.empty.Add(rv, rowToType leftRow),
                Map.empty,
                [kindEqConstraint leftRow.ElementKind rightRow.ElementKind]
            | _ -> raise (UnifyRowRigidMismatch (rowToType leftRow, rowToType rightRow))
        | [], rs ->
            match leftRow.RowEnd with
            | Some lv ->
                Map.empty.Add(lv, rowToType rightRow),
                Map.empty,
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
                unifyDecompose [
                    typeEqConstraint lElem rElem;
                    rowEqConstraint { leftRow with Elements = lRest } { rightRow with Elements = rRest }]
            else
                // no overlapping labels, which means the rows can be concatenated with a new row
                // variable at the end, but only if the row variables are not the same. In the
                // latter case we know the rows cannot possibly unify
                match leftRow.RowEnd, rightRow.RowEnd with
                | Some lv, Some rv when lv = rv -> raise (UnifyRowRigidMismatch (rowToType leftRow, rowToType rightRow))
                | Some lv, Some rv ->
                    let freshVar = fresh.Fresh "r"
                    Map.empty
                        .Add(lv, typeSubstSimplifyExn fresh (Map.empty.Add(rv, typeVar freshVar (KRow rightRow.ElementKind))) (rowToType rightRow))
                        .Add(rv, typeSubstSimplifyExn fresh (Map.empty.Add(lv, typeVar freshVar (KRow leftRow.ElementKind))) (rowToType leftRow)),
                    Map.empty,
                    [kindEqConstraint leftRow.ElementKind rightRow.ElementKind]
                | _ -> raise (UnifyRowRigidMismatch (rowToType leftRow, rowToType rightRow))

    /// Partially solve a single constraint, returning a substitution that partially unifies the constraint,
    /// and any more steps that need to be taken to fully solve the constraint.
    let solveStep fresh uc =
        match uc with
        | UCKind (lk, rk) -> unifyKind lk rk
        | UCTypeSyn (lt, rt) -> unifyType lt rt
        | UCTypeBool (lb, rb, bk) -> unifyBoolean lb rb bk
        | UCTypeFixed (lf, rf) -> unifyFixed fresh lf rf
        | UCTypeAbelian (la, ra, ak) -> unifyAbelian fresh la ra ak
        | UCTypeSeq (ls, rs) -> unifySequence fresh ls rs
        | UCTypeRow (lr, rr) -> unifyRow fresh lr rr
    
    /// Solve the given list of constraints from front to back. Returns the substitution
    /// that represents the most general unifier for all the constraints.
    let solveAll fresh constraints =
        let rec solveConstraint cs typeSubst kindSubst =
            match cs with
            | [] -> typeSubst, kindSubst
            | c :: cs ->
                //printfn $"Unifying {c}"
                let typeUnifier, kindUnifier, decomposed = solveStep fresh c
                let kindComposeUnifier = composeKindSubst kindUnifier kindSubst
                let typeComposeUnifier = composeSubstExn fresh typeUnifier typeSubst
                let typeKindUnifier = Map.map (fun _ t -> typeKindSubstExn kindComposeUnifier t) typeComposeUnifier
                let replaced = List.map (constraintSubstExn fresh kindComposeUnifier typeKindUnifier) (List.append decomposed cs)
                solveConstraint replaced typeKindUnifier kindComposeUnifier
        solveConstraint constraints Map.empty Map.empty
    
    /// Compute the substitution that represents the most general unifier for the two given types.
    /// The resulting substitution may contain mappings from kind variables to kinds if there were
    /// any kind variables in either supplied type.
    let typeUnifyExn fresh l r =
        solveAll fresh [typeEqConstraint l r]
    
    /// Return whether two types can unify.
    let typeOverlap fresh l r =
        try
            typeUnifyExn fresh l r |> constant true
        with
            | _ -> false
    
    /// Compute the substitution that represents the most general unifier for the two given kinds.
    let kindUnifyExn fresh l r =
        solveAll fresh [kindEqConstraint l r]