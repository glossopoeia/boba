namespace Boba.Core

module Boolean =
    
    open System.Diagnostics
    open Common
    
    /// Represents a Boolean equation with variables and the standard Boolean constants. How these constants and variables are
    /// interpreted is up to the consumer of this data type. For Boba, though, we include dotted variables, which are generally
    /// substituted with a sequence that is converted to nested disjunctions. There is also a distinction between rigid and flexible
    /// variables: only flexible variables are considered 'free', and thus only they will be included in the unifier during unification.
    /// This enables us to do 'boolean matching' by setting one side of the equation to rigid, and the other flexible.
    [<DebuggerDisplay("{ToString()}")>]
    type Equation =
        | BTrue
        | BFalse
        | BVar of string
        | BDotVar of string
        | BRigid of string
        | BDotRigid of string
        | BNot of Equation
        | BAnd of Equation * Equation
        | BOr of Equation * Equation
        override this.ToString () =
            match this with
            | BTrue -> "1"
            | BFalse -> "0"
            | BVar n -> n
            | BDotVar n -> $"{n}..."
            | BRigid n -> $"{n}*"
            | BDotRigid n -> $"{n}*..."
            | BNot b ->
                match b with
                | BAnd _ -> $"!({b})"
                | BOr _ -> $"!({b})"
                | _ -> $"!{b}"
            | BAnd (l, r) ->
                match l, r with
                | BOr _, BOr _ -> $"({l})∧({r})"
                | BOr _, _ -> $"({l})∧{r}"
                | _, BOr _ -> $"{l}∧({r})"
                | _, _ -> $"{l}∧{r}"
            | BOr (l, r) ->
                match l, r with
                | BAnd _, BAnd _ -> $"({l})∨({r})"
                | BAnd _, _ -> $"({l})∨{r}"
                | _, BAnd _ -> $"{l}∨({r})"
                | _, _ -> $"{l}∨{r}"

    let mkNot b =
        match b with
        | BFalse -> BTrue
        | BTrue -> BFalse
        | BNot s -> s
        | _ -> BNot b

    let mkNotV v = mkNot (BVar v)
    
    let mkAnd l r =
        match l, r with
        | BTrue, _ -> r
        | _, BTrue -> l
        | BFalse, _ -> BFalse
        | _, BFalse -> BFalse
        | _ when l = r -> l
        | _ when l = BNot r -> BFalse
        | _ when BNot l = r -> BFalse
        | _, BOr (sl, sr) when l = sl || l = sr -> l
        | BOr (sl, sr), _ when r = sl || r = sr -> r
        | _ -> BAnd (l, r)

    let mkAndV l r = mkAnd (BVar l) (BVar r)

    let mkOr l r =
        match l, r with
        | BTrue, _ -> BTrue
        | _, BTrue -> BTrue
        | BFalse, _ -> r
        | _, BFalse -> l
        | _ when l = r -> l
        | _ when l = BNot r -> BTrue
        | _ when BNot l = r -> BTrue
        | _, BAnd (sl, sr) when l = sl || l = sr -> l
        | BAnd (sl, sr), _ when r = sl || r = sr -> r
        | _ -> BOr (l, r)

    let mkOrV l r = mkOr (BVar l) (BVar r)

    let mkXor l r =
        mkOr (mkAnd l (mkNot r)) (mkAnd (mkNot l) r)

    /// Make all variables in the equation flexible.
    let rec flexify eqn =
        match eqn with
        | BRigid n -> BVar n
        | BDotRigid n -> BDotVar n
        | BNot b -> BNot (flexify b)
        | BAnd (l, r) -> BAnd (flexify l, flexify r)
        | BOr (l, r) -> BOr (flexify l, flexify r)
        | _ -> eqn

    /// Make all variables in the equation rigid.
    let rec rigidify eqn =
        match eqn with
        | BVar n -> BRigid n
        | BDotVar n -> BDotRigid n
        | BNot b -> BNot (rigidify b)
        | BAnd (l, r) -> BAnd (rigidify l, rigidify r)
        | BOr (l, r) -> BOr (rigidify l, rigidify r)
        | _ -> eqn
    
    /// Compute the set of free variables in the equation.
    let rec free eqn =
        match eqn with
        | BVar n -> Set.singleton n
        | BDotVar n -> Set.singleton n
        | BNot b -> free b
        | BAnd (l, r) -> Set.union (free l) (free r)
        | BOr (l, r) -> Set.union (free l) (free r)
        | _ -> Set.empty
    
    let rec freeWithCtor eqn =
        match eqn with
        | BVar n -> Map.add n BVar Map.empty
        | BDotVar n -> Map.add n BDotVar Map.empty
        | BNot b -> freeWithCtor b
        | BAnd (l, r) -> mapUnion fst (freeWithCtor l) (freeWithCtor r)
        | BOr (l, r) -> mapUnion fst (freeWithCtor l) (freeWithCtor r)
        | _ -> Map.empty

    /// Replace the given variable with sub in the target Boolean equation.
    let rec substitute var sub target =
        match target with
        | BVar n when n = var -> sub
        | BDotVar n when n = var -> sub
        | BNot b -> mkNot (substitute var sub b)
        | BAnd (l, r) -> mkAnd (substitute var sub l) (substitute var sub r)
        | BOr (l, r) -> mkOr (substitute var sub l) (substitute var sub r)
        | _ -> target

    /// Perform several successive substitution operations on the target equation.
    let applySubst subst target =
        Map.fold (fun eqn var sub -> substitute var sub eqn) target subst
    
    /// Combine two substitutions into a single substitution, such that applying them both separately has the same effect as applying the combined one.
    let mergeSubst subl subr = mapUnion fst subl subr

    /// Compute the truth set for the given equation as a list of BTrue or BFalse.
    let rec truthRow eqn freeVs =
        match freeVs with
        | [] ->
            if eqn = BTrue || eqn = BFalse then [eqn] else [eqn]
        | v :: vs ->
            let vTrue = truthRow (substitute v BTrue eqn) vs
            let vFalse = truthRow (substitute v BFalse eqn) vs
            List.append vTrue vFalse
    
    /// Compute the truth table for the given equation, returning a two dimensional list of the
    /// form [[T, T, ..., T],...,[F, F,..., T]] where the last element in each sublist is the
    /// truth value of the equation for that row.
    let rec truthTable eqn freeVs =
        match freeVs with
        | [] ->
            if eqn = BTrue || eqn = BFalse then [[eqn]] else [[eqn]]
        | v :: vs ->
            let vTrue = truthTable (substitute v BTrue eqn) vs |> List.map (fun r -> BTrue :: r)
            let vFalse = truthTable (substitute v BFalse eqn) vs |> List.map (fun r -> BFalse :: r)
            List.append vTrue vFalse

    /// Compute the truth set for the given equation as an integer where each bit is a truth value.
    /// For example, (a ∨ b) has truth row 1110 = 14. The integer representation allows us to handle
    /// up to 5 variables in an equation.
    let rec truthId eqn freeVs =
        match freeVs with
        | [] -> if eqn = BTrue then 1 else 0
        | v :: vs ->
            let vTrue = truthId (substitute v BTrue eqn) vs
            let vFalse = truthId (substitute v BFalse eqn) vs
            let shift = vs.Length + 1
            (vTrue <<< shift) ||| vFalse

    /// Finds the corresponding minimal equation for any given equation with up to 5 variables
    /// in the given table of minimal equations. If an entry is not found, simply returns the
    /// original equation.
    let lookupMinimal table eqn =
        let freeVsMap = freeWithCtor eqn
        let freeVs = Map.toList freeVsMap |> Seq.map fst |> Seq.toList

        let truth = truthRow eqn freeVs
        // does it contain rigid terms?
        if not (List.forall (fun r -> r = BTrue || r = BFalse) truth)
        then eqn
        // easy case when all are true works for any number of variables
        elif List.forall (fun r -> r = BTrue) truth
        then BTrue
        // easy case when all are false works for any number of variables
        elif List.forall (fun r -> r = BFalse) truth
        then BFalse
        else
            if freeVs.Length > 5
            then eqn
            else
                let id = truthId eqn freeVs
                if Map.containsKey freeVs.Length table && Map.containsKey id (table.[freeVs.Length])
                then
                    let min = (table.[freeVs.Length]).[id]
                    // Must replace minimal eqn variables with corresponding variables from given eqn
                    // This replacement relies on the variables being ordered properly in the minimal eqn
                    let subst = Map.ofList [for i in 0..freeVs.Length-1 -> "x" + i.ToString(), (freeVsMap.[freeVs.[i]]) freeVs.[i]]
                    applySubst subst min
                else eqn

    /// Attempts to minimize the given equation according to a table that may contain
    /// a minimized equivalent. Optionally able to minimize subparts of larger equations
    /// that have no equivalent in the table by setting `recurse` to true.
    let minimizeWith table recurse eqn =
        let rec minRec eqn =
            match eqn with
            | BNot b -> lookupMinimal table (mkNot (minRec b))
            | BAnd (l, r) -> lookupMinimal table (mkAnd (minRec l) (minRec r))
            | BOr (l, r) -> lookupMinimal table (mkOr (minRec l) (minRec r))
            | _ -> eqn
        if recurse then minRec eqn else lookupMinimal table eqn
    
    let minTables = Map.ofList [
        (1, Map.ofList [
            (0b00, BFalse)
            (0b10, BVar "x0")
            (0b01, mkNotV "x0")
            (0b11, BTrue)
        ]);
        (2, Map.ofList [
            (0b0000, BFalse)
            (0b0001, mkAnd (mkNotV "x0") (mkNotV "x1"))
            (0b0010, mkAnd (mkNotV "x0") (BVar "x1"))
            (0b0011, mkNotV "x0")
            (0b0100, mkAnd (BVar "x0") (mkNotV "x1"))
            (0b0101, mkNotV "x1")
            (0b0110, mkAnd (mkOr (mkNotV "x0") (mkNotV "x1")) (mkOrV "x0" "x1"))
            (0b0111, mkOr (mkNotV "x0") (mkNotV "x1"))
            (0b1000, mkAndV "x0" "x1")
            (0b1001, mkOr (mkAnd (mkNotV "x0") (mkNotV "x1")) (mkAndV "x0" "x1"))
            (0b1010, BVar "x1")
            (0b1011, mkOr (mkNotV "x0") (BVar "x1"))
            (0b1100, BVar "x0")
            (0b1101, mkOr (BVar "x0") (mkNotV "x1"))
            (0b1110, mkOrV "x0" "x1")
            (0b1111, BTrue)
        ]);
        (3, Map.ofList [
            (0b00000000, BFalse)
            (0b00000001, mkAnd (mkNotV "x0") (mkAnd (mkNotV "x1") (mkNotV "x2")))
            (0b00000010, mkAnd (mkNotV "x0") (mkAnd (mkNotV "x1") (BVar "x2")))
            (0b00000011, mkAnd (mkNotV "x0") (mkNotV "x1"))
            (0b00000100, mkAnd (mkNotV "x0") (mkAnd (BVar "x1") (mkNotV "x2")))
            (0b00000101, mkAnd (mkNotV "x0") (mkNotV "x2"))
            (0b00000110, mkAnd (mkNotV "x0") (mkAnd (mkOr (mkNotV "x1") (mkNotV "x2")) (mkOrV "x1" "x2")))
            (0b00000111, mkAnd (mkNotV "x0") (mkOr (BVar "x1") (mkNotV "x2")))
            (0b00001000, mkAnd (mkNotV "x0") (mkAndV "x1" "x2"))
            (0b00001001, mkAnd (mkNotV "x0") (mkOr (mkAnd (mkNotV "x1") (mkNotV "x2")) (mkAndV "x1" "x2")))
            (0b00001010, mkAnd (mkNotV "x0") (BVar "x2"))
            (0b00001011, mkAnd (mkNotV "x0") (mkOr (mkNotV "x1") (BVar "x2")))
            (0b00001100, mkAnd (mkNotV "x0") (BVar "x1"))
            (0b00001101, mkAnd (mkNotV "x0") (mkOr (BVar "x1") (mkNotV "x2")))
            (0b00001110, mkAnd (mkNotV "x0") (mkOrV "x1" "x2"))
            (0b00001111, mkNot (BVar "x0"))
            (0b00010000, mkAnd (BVar "x0") (mkAnd (mkNotV "x1") (mkNotV "x2")))
            (0b00010001, mkAnd (mkNotV "x1") (mkNotV "x2"))
            (0b00010010, mkAnd (mkNotV "x1") (mkAnd (mkOr (mkNotV "x0") (mkNotV "x2")) (mkOrV "x0" "x2")))
            (0b00010011, mkAnd (mkNotV "x1") (mkOr (mkNotV "x0") (BVar "x2")))
            (0b00010100, mkAnd (mkNotV "x2") (mkAnd (mkOr (mkNotV "x0") (mkNotV "x1")) (mkOrV "x0" "x1")))
            (0b00010101, mkAnd (mkNotV "x2") (mkOr (mkNotV "x0") (mkNotV "x1")))
            (0b00010110, mkAnd (mkOr (mkNotV "x0") (mkNotV "x1")) (mkOr (mkAnd (mkNotV "x0") (mkAnd (mkNotV "x1") (BVar "x2"))) (mkAnd (mkNotV "x2") (mkOrV "x0" "x1"))))
            (0b00010111, mkOr (mkAnd (mkNotV "x0") (mkNotV "x1")) (mkAnd (mkNotV "x2") (mkOr (mkNotV "x0") (mkNotV "x1"))))
            (0b00011000, mkAnd (mkOr (mkNotV "x0") (mkNotV "x1")) (mkOr (mkAnd (BVar "x0") (mkNotV "x2")) (mkAndV "x1" "x2")))
            (0b00011001, mkOr (mkAnd (mkNotV "x1") (mkNotV "x2")) (mkAnd (mkNotV "x0") (mkAndV "x1" "x2")))
            (0b00011010, mkAnd (mkOr (mkNotV "x0") (mkNotV "x2")) (mkOr (BVar "x2") (mkAnd (BVar "x0") (mkNotV "x1"))))
            (0b00011011, mkAnd (mkOr (mkNotV "x0") (mkNotV "x2")) (mkOr (mkNotV "x1") (BVar "x2")))
            (0b00011100, mkAnd (mkOr (mkNotV "x0") (mkNotV "x1")) (mkOr (BVar "x1") (mkAnd (BVar "x0") (mkNotV "x2"))))
            (0b00011101, mkAnd (mkOr (mkNotV "x0") (mkNotV "x1")) (mkOr (BVar "x1") (mkNotV "x2")))
            (0b00011110, mkAnd (mkOr (mkNotV "x0") (mkAnd (mkNotV "x1") (mkNotV "x2"))) (mkOr (BVar "x0") (mkOrV "x1" "x2")))
            (0b00011111, mkOr (mkNotV "x0") (mkAnd (mkNotV "x1") (mkNotV "x2")))
            (0b00100000, mkAnd (BVar "x0") (mkAnd (mkNotV "x1") (BVar "x2")))
            // TODO: add the rest of these, they're critical to more readable inferred boolean types
            (0b11111110, mkOr (BVar "x0") (mkOrV "x1" "x2"))
            (0b11111111, BTrue)
        ]);
        (4, Map.ofList [
            (0b0000000000000000, BFalse)
            (0b0000000000000001, mkAnd (BVar "x0") (mkAnd (BVar "x1") (mkAndV "x2" "x3")))
            (0b1111111111111110, mkOr (BVar "x0") (mkOr (BVar "x1") (mkOrV "x2" "x3")))
            (0b1111111111111111, BTrue)
        ])
    ]

    let minimize eqn = minimizeWith minTables true eqn

    /// Perform substitution (see substitute) then simplify the equation to keep it small.
    let substituteAndMinimize var sub target = substitute var sub target |> minimize

    /// Eliminate variables one by one by substituting them away
    /// and builds up a resulting substitution. Core of unification.
    let rec private successiveVariableElimination eqn vars =
        match vars with
        | [] ->
            // check whether any remaining rigid variables in the equation make it satisfiable
            if not (satisfiable eqn)
            then Some Map.empty
            else None
        | v :: vs ->
            let vFalse = substitute v BFalse eqn
            let vTrue = substitute v BTrue eqn
            let substRes = successiveVariableElimination (mkAnd vFalse vTrue) vs
            match substRes with
            | None -> None
            | Some subst ->
                let vsub = mkOr (applySubst subst vFalse) (mkAnd (BVar v) (mkNot (applySubst subst vTrue)))
                mergeSubst (Map.empty.Add(v, vsub)) subst |> Some

    /// Checks whether a given equation is satisfiable, i.e. whether there is a substitution of all variables to T or F that makes the equation T when evaluated.
    and satisfiable eqn =
        match minimize eqn with
        | BTrue -> true
        | BFalse -> false
        | _ ->
            let flexed = mkXor (flexify eqn) BTrue
            successiveVariableElimination flexed (free flexed |> Set.toList)
            |> Option.map (constant true)
            |> Option.defaultValue false

    /// Generate a most-general substitution that, when applied to both input equations,
    /// makes them equivalent boolean equations.
    let unify eqnl eqnr =
        // turn it into one equation to perform successive variable elimination
        let eqn = mkXor eqnl eqnr
        // find whichever side has fewer free variables, and eliminate those variables first
        // to yield a smaller unifier
        let lfree = free eqnl
        let rfree = free eqnr
        let sveVars =
            if rfree.Count < lfree.Count
            then List.append (List.ofSeq rfree) (List.ofSeq (Set.difference lfree rfree))
            else List.append (List.ofSeq lfree) (List.ofSeq (Set.difference rfree lfree))
        successiveVariableElimination eqn sveVars
        |> Option.map (mapValues minimize)