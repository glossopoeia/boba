namespace Boba.Core

module Linear =

    open Common

    type Equation = { Coefficients: List<int>; Constants: List<int> }

    /// Find the smallest non-zero coefficient by absolute value and return it and the index at which it was found.
    let private smallest coeffs =
        let chooseSmaller (prevI, prevN) (testI, testN) =
            if prevN = 0
            then (testI, testN)
            elif testN = 0 || abs prevN <= abs testN
            then (prevI, prevN)
            else (testI, testN)
        List.mapi (fun i c -> (i, c)) coeffs
        |> List.fold chooseSmaller (-1, 0)
        
    /// Negate all the integers in a list.
    let private invert = List.map (~-)

    /// Replace the integer at index i in a list with 0.
    let private zeroAt index ls = List.mapi (fun i e -> if index = i then 0 else e) ls

    /// Check if every number in a list is divisible by a given divisor.
    let private divisible divisor ns = List.forall (fun n -> modulo n divisor = 0) ns

    /// Divide every number in a list by the given divisor.
    let private divide divisor ns = List.map (fun n -> div_floor n divisor) ns

    /// Eliminate a variable from the substitution. If the variable is in the original problem,
    /// add it to the substitution.
    let private eliminate v (i, orig) subst =
        let rec addMul n xs ys =
            match n, xs, ys with
            | 1, [], ys -> ys
            | n, [], ys -> List.map ((*) n) ys
            | _, xs, [] -> xs
            | n, x :: xs, y :: ys -> x + n * y :: addMul n xs ys
        // eliminate i from eqn if it occurs in eqn
        let elim eqn =
            if i >= eqn.Coefficients.Length
            then eqn
            elif eqn.Coefficients.[i] = 0
            then eqn
            else { Coefficients = addMul eqn.Coefficients.[i] (zeroAt i eqn.Coefficients) orig.Coefficients;
                   Constants = addMul eqn.Coefficients.[i] eqn.Constants orig.Constants }
        if i < v
        then Map.add i orig (Map.map (constant elim) subst)
        else Map.map (constant elim) subst

    let rec private solveLoop originalEqnVarCount eqn subst =
        let (si, sc) = smallest eqn.Coefficients
        // make sure smallest coefficient is positive
        if sc < 0
        then solveLoop originalEqnVarCount { Coefficients = invert eqn.Coefficients; Constants = invert eqn.Constants } subst
        // no coefficient is an internal error
        elif sc = 0
        then None
        // solution found, eliminate the variable
        elif sc = 1
        then Some (eliminate originalEqnVarCount (si, { Coefficients = invert (zeroAt si eqn.Coefficients); Constants = eqn.Constants }) subst)
        // if both coefficients and constants are divisible, there's a solution
        // if coefficients but not constants are divisible, there can't be a solution
        elif divisible sc eqn.Coefficients
        then
            if divisible sc eqn.Constants
            then
                let coeffs = divide sc eqn.Coefficients
                let consts = divide sc eqn.Constants
                Some (eliminate originalEqnVarCount (si, { Coefficients = invert (zeroAt si coeffs); Constants = consts }) subst)
            else
                None
        // introduce a new variable and solve
        else
            let coeffs = divide sc (zeroAt si eqn.Coefficients)
            let newSubst = eliminate originalEqnVarCount (si, { Coefficients = List.append (invert coeffs) [1]; Constants = [] }) subst
            solveLoop originalEqnVarCount { Coefficients = List.append (List.map (fun m -> modulo m sc) eqn.Coefficients) [sc]; Constants = eqn.Constants } newSubst

    /// Find a solution for the equation, if one exists.
    let solve eqn =
        solveLoop (List.length eqn.Coefficients) eqn Map.empty