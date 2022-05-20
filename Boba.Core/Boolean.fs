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

    type MinTermRow = { Name: Set<int>; Row: List<int>; }

    [<Literal>]
    let QmcTrue = 1
    [<Literal>]
    let QmcFalse = 0
    [<Literal>]
    let QmcDash = 2

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

    let eqnToQmc eqn =
        match eqn with
        | BTrue -> QmcTrue
        | BFalse -> QmcFalse
        | _ -> failwith $"Cannot convert term {eqn} to efficient QMC representation"
    
    let truthRowToInt =
        // take advantage of QMC representation to not have a branch for true/false here
        List.mapi (fun i e -> e <<< i) >> List.sum

    let rowNameEqual l r = l.Name = r.Name

    let minTermTrueCount minTerm =
        List.sumBy (fun e -> if e = QmcTrue then 1 else 0) minTerm.Row
    
    let rowDashCount =
        List.sumBy (fun e -> if e = QmcDash then 1 else 0)

    let tryGenerateComparedRow (left: List<int>) (right: List<int>) =
        let mutable difference = false
        let mutable tooMany = false
        let mutable row = []
        for i in 0..(left.Length-1) do
            if left.[i] <> right.[i]
            then
                // have we already seen a difference? if so, these rows are too different
                if difference
                then tooMany <- true
                else
                    difference <- true
                    row <- List.append row [QmcDash]
            else
                row <- List.append row [left.[i]]
        if difference && not tooMany
        then {| Compared = true; Row = row |}
        else {| Compared = false; Row = [] |}
    
    let compareRowAgainstOthers row otherRows expectedDashes =
        let zipped = [
            for o in otherRows do
                let cmp = tryGenerateComparedRow row.Row o.Row
                if cmp.Compared
                then yield ({ Name = Set.union row.Name o.Name; Row = cmp.Row }, o)
        ]
        List.unzip zipped

    let toTerm (free : List<string * (string -> Equation)>) ind eqn =
        let var, ctor = free.[ind]
        match eqn with
        | QmcTrue -> [ctor var]
        | QmcFalse -> [BNot (ctor var)]
        | _ -> []

    let toSum terms = List.fold mkAnd BTrue terms

    let toProduct sums = List.fold mkOr BFalse sums
    
    let primeImplicants minTerms =
        let rec implicantsIter steps primeImplicants remaining =
            let mutable newChecked = []
            let mutable newRemaining = []
            for i in 0 .. List.length remaining - 2 do
                for minTerm in remaining.[i] do
                    let implicants, matched = compareRowAgainstOthers minTerm remaining.[i+1] steps
                    if matched.Length > 0
                    then newChecked <- minTerm :: newChecked
                    newChecked <- List.append newChecked matched
                    newRemaining <- List.append implicants newRemaining
            newChecked <- List.distinctBy (fun c -> c.Row) newChecked
            newRemaining <- List.distinctBy (fun c -> c.Row) newRemaining
            let primes = [
                for g in remaining do
                    for e in g do
                        // if the row wasn't checked, it's a prime implicant
                        if not (List.exists (fun c -> e.Name = c.Name) newChecked)
                        then yield e]
            let grouped = List.groupBy minTermTrueCount newRemaining |> List.map snd
            checkContinue (steps + 1) (List.append primes primeImplicants) newChecked grouped
        and checkContinue steps primeImplicants checkedImplicants remaining =
            match checkedImplicants with
            | [] -> primeImplicants
            | _ -> implicantsIter steps primeImplicants remaining
        
        let grouped = List.groupBy minTermTrueCount minTerms |> List.map snd
        let implicants = implicantsIter 1 [] grouped
        // bigger names in front, so that de-duplicating chooses the one that covers the most minTerms
        let sorted = List.sortBy (fun imp -> -(Set.count imp.Name)) implicants
        List.distinctBy (fun c -> c.Row) sorted
    
    let essentialImplicants primes minTerms =
        let zipped = [
            for m in minTerms do
                let checks = List.filter (fun p -> Set.isSubset m.Name p.Name) primes
                if List.length checks = 1
                then (checks.[0], checks.[0].Name)
        ]
        let essentials, covered = List.unzip zipped
        let covered = Set.unionMany covered
        // determine which prime implicants and minterms are remaining to be investigated
        let remaining = List.filter (fun p -> not (List.exists (fun e -> p.Name = e.Name) essentials)) primes
        let uncovered = List.filter (fun m -> not (Set.isSubset m.Name covered)) minTerms
        essentials, covered, remaining, uncovered
    
    let productOfSums primes minTerms =
        [for m in minTerms ->
            [for p in primes do
                if Set.isSubset m.Name p.Name
                then yield p.Name]]
    
    let isSubset cmp test =
        List.forall (fun prime -> List.contains prime cmp) test
    
    let reduceByAbsorption sums =
        let mutable reduced = []
        let mutable sumCopy = List.map id sums
        while sumCopy.Length > 0 do
            let product = sumCopy.Head
            if not (List.exists (isSubset product) sumCopy || List.exists (isSubset product) reduced)
            then reduced <- product :: reduced
        reduced
    
    let productOfSumsToSumOfProducts product =
        let mutable sums = [List.head product]
        let mutable prodCopy = List.map id product
        while prodCopy.Length > 0 do
            let term = prodCopy.Head
            let mutable newSums = []
            for t in term do
                for s in sums do
                    if List.contains t s
                    then newSums <- s :: newSums
                    else newSums <- (t :: s) :: newSums
            sums <- newSums
        reduceByAbsorption sums

    let petricks primes minTerms =
        let product = productOfSums primes minTerms
        let sum = productOfSumsToSumOfProducts product
        let sorted = List.sortBy List.length sum
        [for name in sorted.Head -> List.filter (fun p -> p.Name = name) primes |> List.head]

    let minimize eqn =
        let fvs = freeWithCtor eqn |> Map.toList
        let truth = truthTable eqn (List.map fst fvs)

        // does it contain rigid terms?
        if not (List.forall (fun r -> r = BTrue || r = BFalse) (truthRow eqn (List.map fst fvs)))
        then eqn
        else

        // minTerms are elements of the truth table where the result is T.
        // It is convenient to not include the truth value element, so we remove
        // it from each row.
        let minTermRows = [for r in truth do if List.last r = BTrue then yield List.take (List.length r - 1) r]
        // convert to a more efficient representation, and one that supports dashes
        let qmcRows = [for r in minTermRows -> List.map eqnToQmc r]
        // give each minTerm a unique (but meaningful) name to efficiently refer to it later
        let namedMinTerms = [for r in qmcRows -> { Name = Set.singleton (truthRowToInt r); Row = r }]

        let primes = primeImplicants namedMinTerms

        let essentials, covered, remaining, uncovered = essentialImplicants primes namedMinTerms

        let finalImplicants =
            if uncovered <> []
            then
                let covering = petricks remaining uncovered
                List.append essentials covering
            else essentials
        
        // TODO: need to handle dotted vars here
        List.map (fun e -> List.mapi (toTerm fvs) e.Row |> List.concat |> toSum) finalImplicants |> toProduct

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