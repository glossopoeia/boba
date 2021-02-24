namespace Boba.Core

module Predicates =

    open Types
    open Unification

    exception ClassNotInEnvironment of string
    exception ContextReductionFailed of Predicate


    // TODO: remove getClassInstances function when we decide on a single environment structure/type
    let instanceSubgoalsExn fresh pred getClassInstances env =
        match getClassInstances pred.Name env with
        | Some insts ->
            let matching = List.filter (fun i -> isTypeMatch fresh i.Body.Head pred.Argument) insts
            if List.isEmpty matching
            then None
            else
                let first = List.head matching
                let subst = typeMatchExn fresh first.Body.Head pred.Argument
                Some (applySubstContextExn subst first.Body.Context)
        | None -> raise (ClassNotInEnvironment pred.Name)

    // TODO: remove getClassInstances function when we decide on a single environment structure/type
    let rec toHeadNormalFormExn fresh pred getClassInstances env =
        if isPredHeadNoramlForm pred
        then [pred]
        else
            match instanceSubgoalsExn fresh pred getClassInstances env with
            | Some subgoals -> [for sub in subgoals do yield toHeadNormalFormExn fresh sub getClassInstances env] |> List.concat
            | None -> raise (ContextReductionFailed pred)


    // TODO: remove getClassInstances function when we decide on a single environment structure/type
    let rec predEntailsExn fresh pred getClassInstances env =
        match instanceSubgoalsExn fresh pred getClassInstances env with
        | Some subgoals -> List.forall (fun sub -> predEntailsExn fresh sub getClassInstances env) subgoals
        | None -> false

    // TODO: remove getClassInstances function when we decide on a single environment structure/type
    let contextToHeadNormalFormExn fresh context getClassInstances env =
        List.map (fun p -> toHeadNormalFormExn fresh p getClassInstances env) context |> List.concat

    // TODO: remove getClassInstances function when we decide on a single environment structure/type
    let contextSimplifyExn fresh getClassInstances env context =
        let mutable simplified = []
        let mutable remaining = context
        while not (List.isEmpty remaining) do
            let test :: rest = remaining
            if not (predEntailsExn fresh test getClassInstances env)
            then simplified <- test :: simplified
            remaining <- rest
        simplified

    // TODO: remove getClassInstances function when we decide on a single environment structure/type
    let contextReduceExn fresh context getClassInstances env =
        contextToHeadNormalFormExn fresh context getClassInstances env
        |> contextSimplifyExn fresh getClassInstances env