namespace Boba.Core

module QuineMcCluskey =

    open Boba.Core.Boolean

    type MinTermRow = { Name: Set<int>; Row: List<int>; }

    [<Literal>]
    let QmcTrue = 1
    [<Literal>]
    let QmcFalse = 0
    [<Literal>]
    let QmcDash = 2

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
    
    let compareRowAgainstOthers row otherRows expectedDashes =
        let zipped = [
            for o in otherRows do
                let differed = List.mapi (fun i e -> if e = row.Row.[i] then e else QmcDash) o.Row
                if rowDashCount differed = expectedDashes
                then yield ({ Name = Set.union row.Name o.Name; Row = differed }, o)
        ]
        List.unzip zipped

    let toTerm (free : List<string>) ind eqn =
        match eqn with
        | QmcTrue -> [BVar free.[ind]]
        | QmcFalse -> [BNot (BVar free.[ind])]
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
            newChecked <- List.distinctBy (fun c -> c.Name) newChecked
            newRemaining <- List.distinctBy (fun c -> c.Name) newRemaining
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
        let fvs = free eqn |> Set.toList
        let truth = truthTable eqn fvs

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
        
        List.map (fun e -> List.mapi (toTerm fvs) e.Row |> List.concat |> toSum) essentials |> toProduct