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
        | RSimplification of head: List<Type> * result: List<Constraint>
        | RPropagation of head: List<Type> * result: List<Constraint>
        override this.ToString () =
            let comma = ","
            match this with
            | RSimplification (h, cs) -> $"{join h comma} <==> {join cs comma}"
            | RPropagation (h, cs) -> $"{join h comma} ==> {join cs comma}"
    
    type Store =
        { Predicates: Set<Type>; Equalities: Set<TypeConstraint>; }
        override this.ToString () =
            let comma = ","
            $"{{ {join this.Predicates comma}{comma}{join this.Equalities comma} }}"

    let predStore preds = { Predicates = preds; Equalities = Set.empty }

    let constrSubstExn subst constr =
        match constr with
        | CPredicate p -> CPredicate (typeSubstExn subst p)
        | CEquality eqn -> CEquality (constraintSubstExn subst eqn)

    let ruleSubstExn subst rule =
        match rule with
        | RSimplification (hs, rs) ->
            RSimplification (List.map (typeSubstExn subst) hs, List.map (constrSubstExn subst) rs)
        | RPropagation (hs, rs) ->
            RPropagation (List.map (typeSubstExn subst) hs, List.map (constrSubstExn subst) rs)

    let storeSubstExn subst store = {
        Predicates = Set.map (typeSubstExn subst) store.Predicates;
        Equalities = Set.map (constraintSubstExn subst) store.Equalities }

    let constraintFreeWithKinds constr =
        match constr with
        | CPredicate p -> typeFreeWithKinds p
        | CEquality { Left = l; Right = r } -> Set.union (typeFreeWithKinds l) (typeFreeWithKinds r)
    
    let ruleFreeWithKinds rule =
        let freeHeadResult head result = 
            Seq.append (Seq.map typeFreeWithKinds head) (Seq.map constraintFreeWithKinds result)
            |> Seq.fold Set.union Set.empty
        match rule with
        | RSimplification (hs, rs) -> freeHeadResult hs rs
        | RPropagation (hs, rs) -> freeHeadResult hs rs
    
    let freshRule (fresh : FreshVars) rule =
        let quantified = ruleFreeWithKinds rule
        let fresh = fresh.FreshN "f" (Seq.length quantified)
        let freshVars = Seq.zip fresh (Seq.map snd quantified) |> Seq.map TVar
        let freshened = Seq.zip (Seq.map fst quantified) freshVars |> Map.ofSeq
        ruleSubstExn freshened rule



    let addConstraint subst store constr =
        match constr with
        | CPredicate p -> { store with Predicates = Set.add (typeSubstExn subst p) store.Predicates }
        | CEquality eqn -> { store with Equalities = Set.add (constraintSubstExn subst eqn) store.Equalities }

    let applySimplificationToPred fresh preds head result pred =
        try
            let subst = typeMatchExn fresh head pred
            // for simplification, the constraint is removed before adding the applied result
            let remStore = predStore (Set.remove (typeSubstExn subst head) preds)
            List.fold (addConstraint subst) remStore result |> Some
        with
            | ex -> None

    let applyPropagationToPred fresh preds head result pred =
        try
            let subst = typeMatchExn fresh head pred
            // for propagation, the constraint is left in before adding the applied result
            let predStore = predStore preds
            List.fold (addConstraint subst) predStore result |> Some
        with
            | ex -> None

    let applySingleToEach fn preds =
        let unfiltered = Set.map fn preds |> Set.toList |> List.choose id
        let filtered = List.filter (fun s -> s <> predStore preds) unfiltered
        filtered

    let applyRule fresh preds rule =
        match rule with
        | RSimplification ([singleHead], result) ->
            let simpl = applySingleToEach (applySimplificationToPred fresh preds singleHead result) preds
            Seq.iter (fun s -> printfn $"rule {rule} *****> {s}") simpl
            simpl
        | RPropagation ([singleHead], result) ->
            let prop = applySingleToEach (applyPropagationToPred fresh preds singleHead result) preds
            Seq.iter (fun s -> printfn $"rule {rule} *****> {s}") prop
            prop
        | RSimplification ([], _) -> failwith $"Empty simplification rule detected!"
        | RPropagation ([], _) -> failwith $"Empty propagation rule detected!"
        | RSimplification (hs, result) -> failwith $"Multiheaded simplification rules not yet supported."
        | RPropagation (hs, result) -> failwith $"Multiheaded propagation rules not yet supported."

    let rec solvePredicatesIter fresh seen rules store =
        printfn $"==== STEP {List.length seen + 1} ===="
        // Because the unification we employ is unitary, we can perform
        // unification as a prestep to finding applicable rules, knowing
        // that each equation can only produce one MGU so there's no need
        // for branching like there is for rule application
        let subst = solveAll fresh (store.Equalities |> Set.toList)
        printfn $"solved subst: {subst}"
        let substStore = storeSubstExn subst (predStore store.Predicates)
        // Now that we only have predicates, we try to apply each rule to the
        // the store as a step in a derivation path
        printfn $"subst store: {substStore}"
        let stepResults = List.collect (applyRule fresh substStore.Predicates) rules
        printfn $"step results: {stepResults}"
        let unseenResults = List.filter (fun r -> not (List.contains r seen)) stepResults
        printfn $"unseen results: {unseenResults}"
        // If there were no further steps, we can just return here
        if List.isEmpty unseenResults
        then [store.Predicates, subst]
        // Otherwise recurse on the steps applied from here, and filter out results
        // that are the same. This allows us to get a complete set of derivations.
        // If the set of rules are confluent, there will be only one solution.
        else
            List.collect (fun c -> solvePredicatesIter fresh (c :: seen) rules c) unseenResults
            |> List.distinctBy fst
            |> List.map (fun (store, rSubst) -> (store, composeSubstExn rSubst subst))

    let solvePredicates fresh rules preds =
        let freshRules = List.map (freshRule fresh) rules
        solvePredicatesIter fresh [] freshRules (predStore preds)