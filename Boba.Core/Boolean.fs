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
    
    let mkAnd l r =
        match l, r with
        | BTrue, _ -> r
        | _, BTrue -> l
        | BFalse, _ -> BFalse
        | _, BFalse -> BFalse
        | _ when l = r -> l
        | _ when l = BNot r -> BFalse
        | _ when BNot l = r -> BFalse
        | _ -> BAnd (l, r)

    let mkOr l r =
        match l, r with
        | BTrue, _ -> BTrue
        | _, BTrue -> BTrue
        | BFalse, _ -> r
        | _, BFalse -> l
        | _ when l = r -> l
        | _ when l = BNot r -> BTrue
        | _ when BNot l = r -> BTrue
        | _ -> BOr (l, r)

    /// Transform two equations into a solvable Boolean equation form (l xor r = 0)
    let rec equation left right = mkOr (mkAnd left (mkNot right)) (mkAnd (mkNot left) right)

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

    /// Compute the truth set for the given equation as an integer where each bit is a truth value.
    /// For example, (a ∨ b) has truth row 1110 = 14. The integer representation allows us to handle
    /// up to 5 variables in an equation.
    let truthId eqn freeVs =
        let rec truthIdRec eqn freeVs =
            match freeVs with
            | [] -> if eqn = BTrue then 1 else 0
            | v :: vs ->
                let vTrue = truthIdRec (substitute v BTrue eqn) vs
                let vFalse = truthIdRec (substitute v BFalse eqn) vs
                let shift = vs.Length + 1
                (vTrue <<< shift) ||| vFalse
        truthIdRec eqn freeVs

    /// Finds the corresponding minimal equation for any given equation with up to 5 variables
    /// in the given table of minimal equations. If an entry is not found, simply returns the
    /// original equation.
    let lookupMinimal table eqn =
        let freeVs = free eqn |> Set.toList
        let id = truthId eqn freeVs
        if Map.containsKey freeVs.Length table && Map.containsKey id (table.[freeVs.Length])
        then
            let min = (table.[freeVs.Length]).[id]
            // Must replace minimal eqn variables with corresponding variables from given eqn
            // This replacement relies on the variables being ordered properly in the minimal eqn
            let subst = Map.ofList [for i in 0..freeVs.Length-1 -> "x" + i.ToString(), BVar freeVs.[i]]
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
            (0b01, mkNot (BVar "x0"))
            (0b11, BTrue)
        ]);
        (2, Map.ofList [
            (0b0000, BFalse)
            (0b0001, mkAnd (mkNot (BVar "x0")) (mkNot (BVar "x1")))
            (0b0010, mkAnd (mkNot (BVar "x0")) (BVar "x1"))
            (0b0011, mkNot (BVar "x0"))
            (0b0100, mkAnd (BVar "x0") (mkNot (BVar "x1")))
            (0b0101, mkNot (BVar "x1"))
            (0b0110, mkAnd (mkOr (mkNot (BVar "x0")) (mkNot (BVar "x1"))) (mkOr (BVar "x0") (BVar "x1")))
            (0b0111, mkOr (mkNot (BVar "x0")) (mkNot (BVar "x1")))
            (0b1000, mkAnd (BVar "x0") (BVar "x1"))
            (0b1001, mkOr (mkAnd (mkNot (BVar "x0")) (mkNot (BVar "x1"))) (mkAnd (BVar "x0") (BVar "x1")))
            (0b1010, BVar "x1")
            (0b1011, mkOr (mkNot (BVar "x0")) (BVar "x1"))
            (0b1100, BVar "x0")
            (0b1101, mkOr (BVar "x0") (mkNot (BVar "x1")))
            (0b1110, mkOr (BVar "x0") (BVar "x1"))
            (0b1111, BTrue)
        ]);
        (3, Map.ofList [
            (0b00000000, BFalse)
            (0b00000001, mkAnd (mkNot (BVar "x0")) (mkAnd (mkNot (BVar "x1")) (mkNot (BVar "x2"))))
            (0b00000010, mkAnd (mkNot (BVar "x0")) (mkAnd (mkNot (BVar "x1")) (BVar "x2")))
            // TODO: add the rest of these, they're critical to readable inferred boolean types
            (0b11111110, mkOr (BVar "x0") (mkOr (BVar "x1") (BVar "x2")))
            (0b11111111, BTrue)
        ])
    ]

    let minimize eqn = minimizeWith minTables true eqn

    /// Perform substitution (see substitute) then simplify the equation to keep it small.
    let substituteAndMinimize var sub target = substitute var sub target |> minimize

    /// Eliminate variables one by one by substituting them away and builds up a resulting substitution. Core of unification.
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
                let vsub = mkOr (applySubst subst vFalse) (mkAnd (BVar v) (mkNot (applySubst subst vTrue))) |> minimize
                mergeSubst (Map.empty.Add(v, vsub)) subst |> Some

    /// Checks whether a given equation is satisfiable, i.e. whether there is a substitution of all variables to T or F that makes the equation T when evaluated.
    and satisfiable eqn =
        match minimize eqn with
        | BTrue -> true
        | BFalse -> false
        | _ ->
            let flexed = equation (flexify eqn) BTrue
            successiveVariableElimination flexed (free flexed |> Set.toList)
            |> Option.map (constant true)
            |> Option.defaultValue false

    // Is the equation of the form X = eqn, where X not in free(eqn)? If so, generate
    // a simple map [X -> eqn], otherwise return None.
    let rec freeSingleVarAssignment eqnl eqnr =
        match eqnl, eqnr with
        | BVar v, _ when not (Set.contains v (free eqnr)) ->
            Some (Map.add v eqnr Map.empty)
        | _, BVar v when not (Set.contains v (free eqnl)) ->
            Some (Map.add v eqnl Map.empty)
        | _ -> None

    let unifyGeneral eqnl eqnr =
        // turn it into one equation to perform successive variable elimination
        let eqn = equation eqnl eqnr |> minimize
        successiveVariableElimination eqn (List.ofSeq (free eqn))
        |> Option.map (mapValues minimize)

    /// Generate a substitution that, when applied to both input equations,
    /// makes them equivalent boolean equations.
    let unify eqnl eqnr =
        freeSingleVarAssignment eqnl eqnr
        |> Option.orElse (unifyGeneral eqnl eqnr)