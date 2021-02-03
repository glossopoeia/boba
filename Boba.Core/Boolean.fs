namespace Boba.Core

// TODO: Note that if we want to support polymorphically unique tuples, we need to somehow stuff dots into equation data type.
module Boolean =
    
    open System.Diagnostics
    open Common
    
    /// Represents a Boolean equation with variables and the standard Boolean constants. How these constants and variables are
    /// interpreted is up to the consumer of this data type.
    [<DebuggerDisplay("{ToString()}")>]
    type Equation =
        | BTrue
        | BFalse
        | BVar of string
        | BDotVar of string
        | BNot of Equation
        | BAnd of Equation * Equation
        | BOr of Equation * Equation
        override this.ToString () =
            match this with
            | BTrue -> "1"
            | BFalse -> "0"
            | BVar n -> n
            | BDotVar n -> $"{n}..."
            | BNot b -> $"!({b})"
            | BAnd (l, r) -> $"({l} & {r})"
            | BOr (l, r) -> $"({l} | {r})"
    
    /// Compute the set of free variables in the equation.
    let rec free eqn =
        match eqn with
        | BVar n -> Set.singleton n
        | BDotVar n -> Set.singleton n
        | BNot b -> free b
        | BAnd (l, r) -> Set.union (free l) (free r)
        | BOr (l, r) -> Set.union (free l) (free r)
        | _ -> Set.empty
    
    /// Perform many obvious simplification steps to minimize a Boolean equation as much as possible.
    let rec simplify eqn =
        match eqn with
        | BNot n ->
            match simplify n with
            | BFalse -> BTrue
            | BTrue -> BFalse
    
                // !!x -> x
            | BNot b -> b
    
                // !(!x ∨ y) -> (x ∧ !y)
            | BOr (BNot l, r) -> BAnd (l, BNot r)
    
                // !(x ∨ !y) -> (!x ∧ y)
            | BOr (l, BNot r) -> BAnd (BNot l, r)
    
            | b -> BNot b
    
        | BOr (l, r) ->
            match (simplify l, simplify r) with
            | (BTrue, _) -> BTrue
            | (_, BTrue) -> BTrue
    
                // F ∨ x -> x
            | (BFalse, rp) -> rp
    
                // x ∨ F -> x
            | (lp, BFalse) -> lp
    
                // x ∨ x -> x
            | (lp, rp) when lp = rp -> lp
    
                // x ∨ !x -> T
            | (lp, BNot rp) when lp = rp -> BTrue
    
                // !x ∨ x -> T
            | (BNot lp, rp) when lp = rp -> BTrue
    
                // x ∨ (x ∨ y) -> x ∨ y
            | (x1, BOr (x2, y)) when x1 = x2 -> BOr (x1, y)
    
                // x ∨ (y ∨ x) -> x ∨ y
            | (x1, BOr (y, x2)) when x1 = x2 -> BOr (x1, y)
    
                // (x ∨ y) ∨ x -> x ∨ y
            | (BOr (x2, y), x1) when x1 = x2 -> BOr (x1, y)
    
                // (y ∨ x) ∨ x -> x ∨ y
            | (BOr (y, x2), x1) when x1 = x2 -> BOr (x1, y)
    
                // (!x ∨ y) ∨ x -> T
            | (BOr (BNot x1, y), x2) when x1 = x2 -> BTrue
                  
                // (y ∨ !x) ∨ x -> T
            | (BOr (y, BNot x1), x2) when x1 = x2 -> BTrue
    
                // (y ∨ !x) ∨ x -> T
            | (x1, BOr (BNot x2, y)) when x1 = x2 -> BTrue
    
                // (y ∨ !x) ∨ x -> T
            | (x1, BOr (y, BNot x2)) when x1 = x2 -> BTrue
    
                // x ∨ (x ∧ y) -> x
            | (x1, BAnd (x2, y)) when x1 = x2 -> x1
    
                // x ∨ (y ∧ x) -> x
            | (x1, BAnd (y, x2)) when x1 = x2 -> x1
    
                // (x ∧ y) ∨ x -> x
            | (BAnd (x1, y), x2) when x1 = x2 -> x1
    
                // (y ∧ x) ∨ x -> x
            | (BAnd (y, x1), x2) when x1 = x2 -> x1
    
            | (lp, rp) -> BOr (lp, rp)
    
        | BAnd (l, r) ->
            match (simplify l, simplify r) with
            | (BFalse, _) -> BFalse
            | (_, BFalse) -> BFalse
    
                // T ∧ x -> x
            | (BTrue, rp) -> rp
    
                // x ∧ T -> x
            | (lp, BTrue) -> lp
    
                // x ∧ x -> x
            | (lp, rp) when lp = rp -> lp
    
                // x ∧ !x -> F
            | (lp, BNot rp) when lp = rp -> BFalse
    
                // !x ∧ x -> F
            | (BNot lp, rp) when lp = rp -> BFalse
    
                // x ∧ (x ∧ y) -> x ∧ y
            | (x1, BAnd (x2, y)) when x1 = x2 -> BAnd (x1, y)
                  
                // x ∧ (y ∧ x) -> x ∧ y
            | (x1, BAnd (y, x2)) when x1 = x2 -> BAnd (x1, y)
    
                // (x ∧ y) ∧ x -> x ∧ y
            | (BAnd (x1, y), x2) when x1 = x2 -> BAnd (x1, y)
    
                // (y ∧ x) ∧ x -> x ∧ y
            | (BAnd (y, x1), x2) when x1 = x2 -> BAnd (x1, y)
    
                // x ∧ (x ∨ y) -> x
            | (x1, BOr (x2, y)) when x1 = x2 -> x1
    
                // x ∧ (y ∨ x) -> x
            | (x1, BOr (y, x2)) when x1 = x2 -> x1
                
                // (x ∨ y) ∧ x -> x
            | (BOr (x1, y), x2) when x1 = x2 -> x1
                
                // (y ∨ x) ∧ x -> x
            | (BOr (y, x1), x2) when x1 = x2 -> x1
    
                // x ∧ !(x ∨ y) -> F
            | (x1, BNot (BOr (x2, y))) when x1 = x2 -> BFalse
    
                // x ∧ !(y ∨ x) -> F
            | (x1, BNot (BOr (y, x2))) when x1 = x2 -> BFalse
                
                // !(x ∨ y) ∧ x -> F
            | (BNot (BOr (x1, y)), x2) when x1 = x2 -> BFalse
    
                // !(y ∨ x) ∧ x -> F
            | (BNot (BOr (y, x1)), x2) when x1 = x2 -> BFalse
    
                // x ∧ (!x ∧ y) -> F
            | (x1, BAnd (BNot x2, y)) when x1 = x2 -> BFalse
    
                // x ∧ (!x ∧ y) -> F
            | (x1, BAnd (y, BNot x2)) when x1 = x2 -> BFalse
    
                // (!x ∧ y) ∧ x -> F
            | (BAnd (BNot x1, y), x2) when x1 = x2 -> BFalse
    
                // (y ∧ !x) ∧ x -> F
            | (BAnd (y, BNot x1), x2) when x1 = x2 -> BFalse
    
            | (lp, rp) -> BAnd (lp, rp)
        | b -> b
    
    /// Replace the given variable with sub in the target Boolean equation.
    let rec substitute var sub target =
        match target with
        | BVar n when n = var -> sub
        | BVar _ -> target
        | BDotVar n when n = var -> sub
        | BDotVar _ -> target
        | BNot b -> BNot (substitute var sub b)
        | BAnd (l, r) -> BAnd (substitute var sub l, substitute var sub r)
        | BOr (l, r) -> BOr (substitute var sub l, substitute var sub r)
        | _ -> target
    
    /// Perform substitution (see substitute) then simplify the equation to keep it small.
    let substituteAndSimplify var sub target = substitute var sub target |> simplify
    
    /// Perform several successive substitution operations on the target equation.
    let applySubst subst target = Map.fold (fun eqn var sub -> substitute var sub eqn) target subst
    
    /// Combine two substitutions into a single substitution, such that applying them both separately has the same effect as applying the combined one.
    let composeSubst subl subr = Map.map (fun _ v -> applySubst subl v) subr |> mapUnion fst subl
    
    /// Generate a substitution that, when applied to both input equations, makes them equivalent equations.
    let unify eqnl eqnr =
        // turn it into one equation to perform SVE, 
        let eqn = simplify (BOr (BAnd (BNot eqnl, eqnr), BAnd(eqnl, BNot eqnr)))
        // successive variable elimination
        let rec unifyLoop eqn vars =
            match vars with
            | [] -> if eqn = BFalse then Option.Some Map.empty else Option.None
            | v :: vs ->
                let vFalse = substituteAndSimplify v BFalse eqn
                let vTrue = substituteAndSimplify v BTrue eqn
                let substRes = unifyLoop (simplify (BAnd (vFalse, vTrue))) vs
                let vSub f t = BOr (f, BAnd (BVar v, BNot t))
                Option.map
                    (fun subst -> composeSubst subst (Map.add v (simplify (vSub (applySubst subst vFalse) (applySubst subst vTrue))) Map.empty))
                    substRes
        unifyLoop eqn (List.ofSeq (free eqn))