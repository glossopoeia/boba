namespace Boba.Core

(*module Predicates =


    open Types
    open Declarations
    open Environment
    open Unification

    exception ClassNotInEnvironment of string
    exception ContextReductionFailed of Predicate


    // Head noraml form computations
    let rec isTypeHeadNormalForm t =
        match t with
        | TVar _ -> true
        | TDotVar _ -> true
        | TApp (l, _) -> isTypeHeadNormalForm l
        | _ -> false

    let rec isPredHeadNoramlForm p = isTypeHeadNormalForm p.Argument


    // Ambiguity of type context predicates
    let isAmbiguousPredicates preds bound =
        not (Set.isEmpty (Set.difference (contextFree preds) bound))


    let instanceSubgoalsExn fresh (pred : Predicate) env =
        match Environment.lookupClass env pred.Name with
        | Some tc ->
            let matching = List.filter (fun (i : TypeclassInstance) -> isTypeMatch fresh i.Overloaded.Head pred.Argument) tc.Instances
            if List.isEmpty matching
            then None
            else
                let first = List.head matching
                let subst = typeMatchExn fresh first.Overloaded.Head pred.Argument
                Some (applySubstContextExn subst first.Overloaded.Context)
        | None -> raise (ClassNotInEnvironment pred.Name)

    let rec toHeadNormalFormExn fresh env pred =
        if isPredHeadNoramlForm pred
        then [pred]
        else
            match instanceSubgoalsExn fresh pred env with
            | Some subgoals -> List.map (toHeadNormalFormExn fresh env) subgoals |> List.concat
            | None -> raise (ContextReductionFailed pred)


    let rec predEntailsExn fresh pred env =
        match instanceSubgoalsExn fresh pred env with
        | Some subgoals -> List.forall (fun sub -> predEntailsExn fresh sub env) subgoals
        | None -> false

    let contextToHeadNormalFormExn fresh context env =
        List.map (toHeadNormalFormExn fresh env) context |> List.concat

    let contextSimplifyExn fresh env context =
        let mutable simplified = []
        let mutable remaining = context
        while not (List.isEmpty remaining) do
            let test :: rest = remaining
            if not (predEntailsExn fresh test env)
            then simplified <- test :: simplified
            remaining <- rest
        simplified

    let contextReduceExn fresh context env =
        contextToHeadNormalFormExn fresh context env
        |> contextSimplifyExn fresh env 
        
    *)