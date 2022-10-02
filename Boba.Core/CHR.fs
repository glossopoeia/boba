namespace Boba.Core

/// This module contains a quick-and-dirty implementation of Constraint Handling Rules with
/// some differences from the usual description. The only built-in constraint is equality,
/// and we use a set-based semantics rather than multi-set. Currently only single-headed
/// rules are supported.
module CHR =

    open System.Diagnostics
    open Common
    open Fresh
    open Types
    open Kinds
    open Unification

    [<DebuggerDisplay("{ToString()}")>]
    type Constraint =
        | CPredicate of Type
        | CEquality of TypeConstraint
        override this.ToString () =
            match this with
            | CPredicate t -> t.ToString()
            | CEquality eqn -> eqn.ToString()

    [<DebuggerDisplay("{ToString()}")>]
    type Rule =
        | RSimplification of head: List<Type> * result: DotSeq.DotSeq<Constraint>
        | RPropagation of head: List<Type> * result: List<Constraint>
        override this.ToString () =
            let comma = ","
            match this with
            | RSimplification (h, cs) -> $"{join h comma} <==> {cs}"
            | RPropagation (h, cs) -> $"{join h comma} ==> {join cs comma}"

    let simplificationPredicate hs ps =
        RSimplification (hs, DotSeq.map CPredicate ps)

    let simplification hs rs =
        assert (List.forall isTypeWellKinded hs)
        RSimplification (hs, rs)
    
    let isSimplification r =
        match r with
        | RSimplification _ -> true
        | _ -> false

    let propagation hs rs = RPropagation (hs, rs)
    
    type Store =
        { Predicates: Set<Type>; Equalities: Set<TypeConstraint>; }
        override this.ToString () =
            let comma = ","
            $"{{ {join this.Predicates comma}{comma}{join this.Equalities comma} }}"

    let predStore preds = { Predicates = preds; Equalities = Set.empty }

    let constrSubstExn fresh subst constr =
        match constr with
        | CPredicate p -> CPredicate (typeSubstExn fresh subst p)
        | CEquality eqn -> CEquality (constraintSubstExn fresh subst eqn)

    let ruleSubstExn fresh subst rule =
        match rule with
        | RSimplification (hs, rs) ->
            RSimplification (List.map (typeSubstExn fresh subst) hs, DotSeq.map (constrSubstExn fresh subst) rs)
        | RPropagation (hs, rs) ->
            RPropagation (List.map (typeSubstExn fresh subst) hs, List.map (constrSubstExn fresh subst) rs)

    let storeSubstExn fresh subst store = {
        Predicates = Set.map (typeSubstExn fresh subst) store.Predicates;
        Equalities = Set.map (constraintSubstExn fresh subst) store.Equalities }

    let constraintFreeWithKinds constr =
        match constr with
        | CPredicate p -> typeFreeWithKinds p
        | CEquality { Left = l; Right = r } -> Set.union (typeFreeWithKinds l) (typeFreeWithKinds r)
    
    let constraintFree =
        constraintFreeWithKinds >> Set.map fst
    
    let constraintSetMatch fresh ls rs =
        Set.forall (fun l -> Set.exists (fun r -> isTypeMatch fresh l r) rs) ls
    
    let constraintSetEquiv fresh ls rs =
        if Set.count ls = Set.count rs
        then Set.forall (fun l -> Set.exists (fun r -> isTypeMatch fresh l r && isTypeMatch fresh r l) rs) ls
        else false
    
    let ruleFreeWithKinds rule =
        match rule with
        | RSimplification (hs, rs) ->
            Seq.append (Seq.map typeFreeWithKinds hs) (DotSeq.map constraintFreeWithKinds rs |> DotSeq.toList)
            |> Seq.fold Set.union Set.empty
        | RPropagation (hs, rs) ->
            Seq.append (Seq.map typeFreeWithKinds hs) (Seq.map constraintFreeWithKinds rs)
            |> Seq.fold Set.union Set.empty
    
    let freshRule (fresh : FreshVars) rule =
        let quantified = ruleFreeWithKinds rule
        let freshies = fresh.FreshN "f" (Seq.length quantified)
        let freshVars = Seq.zip freshies (Seq.map snd quantified) |> Seq.map TVar
        let freshened = Seq.zip (Seq.map fst quantified) freshVars |> Map.ofSeq
        ruleSubstExn fresh freshened rule



    let addConstraintDot fresh subst isDotted store constr =
        match constr with
        | CPredicate p ->
            assert (isTypeWellKinded p)
            let subbed = typeSubstExn fresh subst p
            match subbed with
            | TSeq _ ->
                let dotStr = if isDotted then "..." else ""
                printfn $"Substituted {p}{dotStr} with {subbed}"
            | _ -> ignore subbed
            if isDotted
            then
                match subbed with
                | TSeq (ts, k) -> { store with Predicates = DotSeq.foldDotted (fun d ps r -> if d then Set.add (TSeq (DotSeq.dot r DotSeq.SEnd, k)) ps else Set.add r ps) store.Predicates ts }
                | t -> { store with Predicates = Set.add t store.Predicates }
            else { store with Predicates = Set.add subbed store.Predicates }
        | CEquality eqn -> { store with Equalities = Set.add (constraintSubstExn fresh subst eqn) store.Equalities }

    let addConstraint fresh subst store constr =
        match constr with
        | CPredicate p ->
            assert (isTypeWellKinded p)
            { store with Predicates = Set.add (typeSubstExn fresh subst p) store.Predicates }
        | CEquality eqn -> { store with Equalities = Set.add (constraintSubstExn fresh subst eqn) store.Equalities }

    let applySimplificationToPred fresh compose preds head result pred =
        try
            let subst = typeMatchExn fresh head pred
            let subst = mergeSubstExn fresh compose subst
            // for simplification, the constraint is removed before adding the applied result
            let remStore = predStore (Set.remove pred preds)
            DotSeq.foldDotted (addConstraintDot fresh subst) remStore result |> Some
        with
            | ex -> 
                //printfn $"Trying {head} against {pred} failed with {ex}"
                None

    let applyPropagationToPred fresh compose preds head result pred =
        try
            let subst = typeMatchExn fresh head pred
            // TODO: should this be mergeSubst?
            let subst = composeSubstExn fresh compose subst
            // for propagation, the constraint is left in before adding the applied result
            let predStore = predStore preds
            List.fold (addConstraint fresh subst) predStore result |> Some
        with
            | ex ->
                //printfn $"Trying {head} against {pred} failed with {ex}"
                None

    let applySingleToEach fn preds =
        let unfiltered = Set.map fn preds |> Set.toList |> List.choose id
        let filtered = List.filter (fun s -> s <> predStore preds) unfiltered
        filtered
    
    let applyMultiToEach fn preds =
        let unfiltered = fn preds
        let filtered = List.filter (fun s -> s <> predStore preds) unfiltered
        filtered

    let rec applySimplificationToPreds fresh subst heads preds results remMatchPreds =
        match heads with
        | [] -> failwith "Empty-headed simplification rule, seems unsound!"
        | [single] -> applySingleToEach (applySimplificationToPred fresh subst preds single results) remMatchPreds
        | h :: hs ->
            [for p in remMatchPreds ->
                try
                    let headSubst = typeMatchExn fresh h p
                    let subst = mergeSubstExn fresh subst headSubst
                    let remMatchPreds = Set.remove p remMatchPreds
                    applySimplificationToPreds fresh subst hs (Set.remove p preds) results remMatchPreds |> Some
                with
                    | ex -> None]
            |> List.choose id
            |> List.concat
    
    let rec applyPropagationToPreds fresh subst heads preds result remMatchPreds =
        match heads with
        | [] -> failwith "Empty-headed propagation rule, seems unsound!"
        | [single] -> applySingleToEach (applyPropagationToPred fresh subst preds single result) remMatchPreds
        | h :: hs ->
            [for p in remMatchPreds ->
                try
                    let headSubst = typeMatchExn fresh h p
                    // TODO: should this be mergeSubst?
                    let subst = composeSubstExn fresh subst headSubst
                    let remMatchPreds = Set.remove p remMatchPreds
                    applyPropagationToPreds fresh subst hs preds result remMatchPreds |> Some
                with
                    | ex -> None]
            |> List.choose id
            |> List.concat

    let applyRule fresh preds rule =
        match rule with
        | RSimplification ([singleHead], result) ->
            let simpl = applySingleToEach (applySimplificationToPred fresh Map.empty preds singleHead result) preds
            //Seq.iter (fun s -> printfn $"rule {rule} *****> {s}") simpl
            simpl
        | RPropagation ([singleHead], result) ->
            let prop = applySingleToEach (applyPropagationToPred fresh Map.empty preds singleHead result) preds
            //Seq.iter (fun s -> printfn $"rule {rule} *****> {s}") prop
            prop
        | RSimplification ([], _) -> failwith $"Empty simplification rule detected!"
        | RPropagation ([], _) -> failwith $"Empty propagation rule detected!"
        | RSimplification (hs, results) -> applyMultiToEach (applySimplificationToPreds fresh Map.empty hs preds results) preds
        | RPropagation (hs, results) -> applyMultiToEach (applyPropagationToPreds fresh Map.empty hs preds results) preds


    let rec solvePredicatesIter fresh seen rules store =
        // At each step, the store may contain constraints and predicates as a result
        // of the last step. We must first solve any constraints and apply the resulting
        // substitutions to the predicates in the store, before further attempting to
        // reduce the store.
        //printfn $"==== STEP {List.length seen + 1} ===="
        // Because the unification we employ is unitary, we can perform
        // unification as a prestep to finding applicable rules, knowing
        // that each equation can only produce one MGU so there's no need
        // for branching like there is for rule application
        let subst = solveAll fresh (store.Equalities |> Set.toList)
        //printfn $"solved subst: {subst}"
        let substStore = storeSubstExn fresh subst (predStore store.Predicates)
        // Now that we only have predicates, we try to apply each rule to the
        // the store as a step in a derivation path
        //printfn $"subst store: {substStore}"
        let stepResults = List.collect (applyRule fresh substStore.Predicates) rules
        //printfn $"step results: {stepResults}"
        let unseenResults = List.filter (fun r -> not (List.contains r seen)) stepResults
        //printfn $"unseen results: {unseenResults}"
        // If there were no further steps, we can just return here
        if List.isEmpty unseenResults
        then [store.Predicates, subst]
        // Otherwise recurse on the steps applied from here, and filter out results
        // that are the same. This allows us to get a complete set of derivations.
        // If the set of rules are confluent, there will be only one solution.
        else
            List.collect (fun c -> solvePredicatesIter fresh (c :: seen) rules c) unseenResults
            |> List.fold (fun uniq constr -> if List.exists (fun o -> constraintSetEquiv fresh (fst o) (fst constr)) uniq then uniq else constr :: uniq) []
            |> List.map (fun (store, rSubst) -> (store, composeSubstExn fresh rSubst subst))

    let solvePredicates fresh rules preds =
        let freshRules = List.map (freshRule fresh) rules
        //Seq.iter (fun r -> printfn $"Rule ===> {r}") freshRules
        solvePredicatesIter fresh [] freshRules (predStore preds)
    
    let solveConstraints fresh rules preds eqs =
        let freshRules = List.map (freshRule fresh) rules
        //Seq.iter (fun r -> printfn $"Rule ===> {r}") freshRules
        solvePredicatesIter fresh [] freshRules { Predicates = preds; Equalities = eqs }