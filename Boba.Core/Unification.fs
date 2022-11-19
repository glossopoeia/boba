namespace Boba.Core

module Unification =
    
    open Common
    open Fresh
    open Kinds
    open Types

    type UnifyConstraint =
        | UCKindEq of Kind * Kind
        | UCKindMatch of Kind * Kind
        | UCTypeEqSyn of Type * Type
        | UCTypeEqBool of Boolean.Equation * Boolean.Equation * Kind
        | UCTypeEqFixed of Abelian.Equation<string, int> * Abelian.Equation<string, int>
        | UCTypeEqAbelian of Abelian.Equation<string, string> * Abelian.Equation<string, string> * Kind
        | UCTypeEqSeq of DotSeq.DotSeq<Type> * DotSeq.DotSeq<Type>
        | UCTypeEqRow of RowType * RowType
        | UCTypeMatchSyn of Type * Type
        | UCTypeMatchBool of Boolean.Equation * Boolean.Equation * Kind
        | UCTypeMatchFixed of Abelian.Equation<string, int> * Abelian.Equation<string, int>
        | UCTypeMatchAbelian of Abelian.Equation<string, string> * Abelian.Equation<string, string> * Kind
        | UCTypeMatchSeq of DotSeq.DotSeq<Type> * DotSeq.DotSeq<Type>
        | UCTypeMatchRow of RowType * RowType
        override this.ToString() =
            match this with
            | UCKindEq (lk, rk) -> $"kind: {lk} ~~ {rk}"
            | UCKindMatch (lk, rk) -> $"kind: {lk} ~> {rk}"
            | UCTypeEqSyn (lt, rt) -> $"type: {lt} ~~ {rt}"
            | UCTypeEqBool (lb, rb, k) -> $"bool {k}: {lb} ~~ {rb}"
            | UCTypeEqFixed (lf, rf) -> $"fixed: {lf} ~~ {rf}"
            | UCTypeEqAbelian (la, ra, ak) -> $"abelian {ak}: {la} ~~ {ra}"
            | UCTypeEqSeq (ls, rs) -> $"seq: {TSeq (ls)} ~~ {TSeq (rs)}"
            | UCTypeEqRow (lr, rr) -> $"row: {lr} ~~ {rr}"
            | UCTypeMatchSyn (lt, rt) -> $"type: {lt} ~> {rt}"
            | UCTypeMatchBool (lb, rb, k) -> $"bool {k}: {lb} ~> {rb}"
            | UCTypeMatchFixed (lf, rf) -> $"fixed: {lf} ~> {rf}"
            | UCTypeMatchAbelian (la, ra, ak) -> $"abelian {ak}: {la} ~> {ra}"
            | UCTypeMatchSeq (ls, rs) -> $"seq: {TSeq (ls)} ~> {TSeq (rs)}"
            | UCTypeMatchRow (lr, rr) -> $"row: {lr} ~> {rr}"
    
    let kindEqConstraint = curry UCKindEq
    let kindMatchConstraint = curry UCKindMatch
    let typeEqConstraint = curry UCTypeEqSyn
    let booleanEqConstraint l r k = UCTypeEqBool (l, r, k)
    let fixedEqConstraint = curry UCTypeEqFixed
    let abelianEqConstraint l r k = UCTypeEqAbelian (l, r, k)
    let sequenceEqConstraint = curry UCTypeEqSeq
    let rowEqConstraint = curry UCTypeEqRow
    let typeMatchConstraint = curry UCTypeMatchSyn
    let booleanMatchConstraint l r k = UCTypeMatchBool (l, r, k)
    let fixedMatchConstraint = curry UCTypeMatchFixed
    let abelianMatchConstraint l r k = UCTypeMatchAbelian (l, r, k)
    let sequenceMatchConstraint = curry UCTypeMatchSeq
    let rowMatchConstraint = curry UCTypeMatchRow

    let constraintFreeWithKinds cnstr =
        match cnstr with
        | UCKindEq _ -> Set.empty
        | UCKindMatch _ -> Set.empty
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
        | UCTypeMatchSyn (lt, rt) ->
            Set.union (typeFreeWithKinds lt) (typeFreeWithKinds rt)
        | UCTypeMatchRow (lr, rr) ->
            Set.union (typeFreeWithKinds (rowToType lr)) (typeFreeWithKinds (rowToType rr))
        | UCTypeMatchSeq (ls, rs) ->
            Set.union (typeFreeWithKinds (typeSeq ls)) (typeFreeWithKinds (typeSeq rs))
        | UCTypeMatchBool (lb, rb, bk) ->
            Set.union
                (typeFreeWithKinds (booleanEqnToType bk lb))
                (typeFreeWithKinds (booleanEqnToType bk rb))
        | UCTypeMatchAbelian (la, ra, ak) ->
            Set.union
                (typeFreeWithKinds (abelianEqnToType ak la))
                (typeFreeWithKinds (abelianEqnToType ak ra))
        | UCTypeMatchFixed (lf, rf) ->
            Set.union (typeFreeWithKinds (fixedEqnToType lf)) (typeFreeWithKinds (fixedEqnToType rf))
    
    let constraintFree cnstr = constraintFreeWithKinds cnstr |> Set.map fst

    let rec constraintSubstExn fresh kSubst tSubst cnstr =
        match cnstr with
        | UCKindEq (lk, rk) -> kindEqConstraint (kindSubst kSubst lk) (kindSubst kSubst rk)
        | UCKindMatch (lk, rk) -> kindMatchConstraint (kindSubst kSubst lk) (kindSubst kSubst rk)
        | UCTypeEqSyn (lt, rt) ->
            let ltk, rtk = typeKindSubstExn kSubst lt, typeKindSubstExn kSubst rt
            typeEqConstraint (typeSubstExn fresh tSubst ltk) (typeSubstExn fresh tSubst rtk)
        | UCTypeEqRow (lr, rr) ->
            let (UCTypeEqSyn (lrs, rrs)) = constraintSubstExn fresh kSubst tSubst (typeEqConstraint (rowToType lr) (rowToType rr))
            rowEqConstraint (typeToRow lrs) (typeToRow rrs)
        | UCTypeEqSeq (ls, rs) ->
            let (UCTypeEqSyn (TSeq lss, TSeq rss)) =
                constraintSubstExn fresh kSubst tSubst (typeEqConstraint (typeSeq ls) (typeSeq rs))
            sequenceEqConstraint lss rss
        | UCTypeMatchSyn (lt, rt) ->
            let ltk, rtk = typeKindSubstExn kSubst lt, typeKindSubstExn kSubst rt
            typeMatchConstraint (typeSubstExn fresh tSubst ltk) (typeSubstExn fresh tSubst rtk)
        | UCTypeMatchRow (lr, rr) ->
            let (UCTypeEqSyn (lrs, rrs)) = constraintSubstExn fresh kSubst tSubst (typeMatchConstraint (rowToType lr) (rowToType rr))
            rowMatchConstraint (typeToRow lrs) (typeToRow rrs)
        | UCTypeMatchSeq (ls, rs) ->
            let (UCTypeEqSyn (TSeq lss, TSeq rss)) =
                constraintSubstExn fresh kSubst tSubst (typeMatchConstraint (typeSeq ls) (typeSeq rs))
            sequenceMatchConstraint lss rss
        // NOTE: this is only valid as bool, fixed, and abelian are solved instantly
        // after being appended to the solve list, and thus are never in the 'to-be-solved'
        // section that has composed substitutions applied to it
        | UCTypeEqBool _ -> cnstr
        | UCTypeEqFixed _ -> cnstr
        | UCTypeEqAbelian _ -> cnstr
        | UCTypeMatchBool _ -> cnstr
        | UCTypeMatchFixed _ -> cnstr
        | UCTypeMatchAbelian _ -> cnstr

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
    
    /// Utility method for when a unification step only breaks down the unification
    /// problem, and does not partially construct the result substitution.
    let constraintDecompose cnstrs = Map.empty, Map.empty, cnstrs

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
            Map.empty, Map.add v rk Map.empty, []
        | _, KVar v ->
            Map.empty, Map.add v lk Map.empty, []
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
            Map.add nl r Map.empty, Map.empty, [kindEqConstraint k (typeKindExn r)]
        | l, TVar (nr, k) ->
            Map.add nr l Map.empty, Map.empty, [kindEqConstraint k (typeKindExn l)]
        | TCon (ln, lk), TCon (rn, rk) when ln = rn ->
            Map.empty, Map.empty, [kindEqConstraint lk rk]
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
            Map.empty, Map.empty, []
        | DotSeq.SInd (li, lss), DotSeq.SInd (ri, rss) ->
            constraintDecompose [typeEqConstraint li ri; sequenceEqConstraint lss rss]
        | DotSeq.SDot (ld, DotSeq.SEnd), DotSeq.SDot (rd, DotSeq.SEnd) ->
            constraintDecompose [typeEqConstraint ld rd]
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SEnd ->
            [for (v, k) in List.ofSeq (typeFreeWithKinds li) do (v, typeSeq DotSeq.SEnd)] |> Map.ofList, Map.empty, []
        | DotSeq.SEnd, DotSeq.SDot (ri, DotSeq.SEnd) ->
            [for (v, k) in List.ofSeq (typeFreeWithKinds ri) do (v, typeSeq DotSeq.SEnd)] |> Map.ofList, Map.empty, []
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SInd _ when not (Set.isEmpty (Set.intersect (typeFree li) (typeFree (TSeq (rs))))) ->
            raise (UnifyTypeOccursCheckFailure (TSeq (ls), TSeq (rs)))
        | DotSeq.SInd _, DotSeq.SDot (ri, DotSeq.SEnd) when not (Set.isEmpty (Set.intersect (typeFree ri) (typeFree (TSeq (ls))))) ->
            raise (UnifyTypeOccursCheckFailure (TSeq (ls), TSeq (rs)))
        | DotSeq.SDot (li, DotSeq.SEnd), DotSeq.SInd (ri, rs) ->
            let freshVars = typeFreeWithKinds li |> List.ofSeq |> genSplitSub fresh
            freshVars,
            Map.empty,
            [typeEqConstraint
                (typeSubstSimplifyExn fresh freshVars (typeSeq (DotSeq.dot li DotSeq.SEnd)))
                (typeSeq (DotSeq.ind ri rs))]
        | DotSeq.SInd (li, ls), DotSeq.SDot (ri, DotSeq.SEnd) ->
            let freshVars = typeFreeWithKinds ri |> List.ofSeq |> genSplitSub fresh
            freshVars,
            Map.empty,
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
                constraintDecompose [kindEqConstraint leftRow.ElementKind rightRow.ElementKind]
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
                constraintDecompose [
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
        | UCKindEq (lk, rk) -> unifyKind lk rk
        | UCTypeEqSyn (lt, rt) -> unifyType lt rt
        | UCTypeEqBool (lb, rb, bk) -> unifyBoolean lb rb bk
        | UCTypeEqFixed (lf, rf) -> unifyFixed fresh lf rf
        | UCTypeEqAbelian (la, ra, ak) -> unifyAbelian fresh la ra ak
        | UCTypeEqSeq (ls, rs) -> unifySequence fresh ls rs
        | UCTypeEqRow (lr, rr) -> unifyRow fresh lr rr
    
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