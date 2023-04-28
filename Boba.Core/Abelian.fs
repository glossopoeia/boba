namespace Boba.Core

module Abelian =

    open System
    open System.Diagnostics
    open Common
    open Fresh

    /// Represents a simple Abelian equation composed of constant values and variables which can each have a signed integer exponent.
    /// The implementation uses dictionaries as a form of signed multiset, where an element in the set can have more than one occurence
    /// (represented by a positive exponent) or even negative occurences (represented by a negative exponent). If an element has exactly zero
    /// occurences, it is removed from the dictionary for efficiency.
    [<DebuggerDisplay("{ToString()}")>]
    type Equation<'a, 'b> when 'a: comparison and 'b: comparison (variables: Map<'a, int>, constants: Map<'b, int>) =

        new(name: 'a) =
            Equation<'a, 'b>(Map.add name 1 Map.empty, Map.empty)

        new() =
            Equation<'a, 'b>(Map.empty, Map.empty)

        /// The set of variables in the unit equation, mapped to their exponents.
        member this.Variables = variables
        /// The set of constants in the unit equation, mapped to their exponents.
        member this.Constants = constants

        member this.IsIdentity () = this.Variables.IsEmpty && this.Constants.IsEmpty

        member this.IsConstant () = this.Variables.IsEmpty

        /// Negates each exponent in the equation.
        member this.Invert () =
            new Equation<'a, 'b>(mapValues (( ~- )) this.Variables, mapValues (( ~- )) this.Constants)

        /// Combine two Abelian unit equations. Values that appear in both equations have their exponents multiplied.
        member this.Add (other: Equation<'a, 'b>) =
            let mergeAdd (v1, v2) = v1 + v2
            let isExponentNonZero _ v = v <> 0
            let vars = mapUnion mergeAdd this.Variables other.Variables |> Map.filter isExponentNonZero
            let constants = mapUnion mergeAdd this.Constants other.Constants |> Map.filter isExponentNonZero
            new Equation<'a, 'b>(vars, constants)

        /// Removes the given equation from this Abelian unit equation. Equivalent to `this.Add(other.Invert())`.
        member this.Subtract (other: Equation<'a, 'b>) = other.Invert() |> this.Add;

        // Get the free variables of this equation.
        member this.Free () = mapKeys this.Variables
        
        member this.FractionString () =
            let expToStr exps =
                Map.map (fun k v -> if v = 1 then $"{k}" else $"{k}^{v}") exps |> Map.toList |> List.map snd
            let posVars = Map.filter (fun k v -> v >= 0) this.Variables |> expToStr
            let posCons = Map.filter (fun k v -> v >= 0) this.Constants |> expToStr
            let negVars = Map.filter (fun k v -> v < 0) this.Variables |> Map.map (fun k v -> -v) |> expToStr
            let negCons = Map.filter (fun k v -> v < 0) this.Constants |> Map.map (fun k v -> -v) |> expToStr
            let pos = String.concat "*" (List.append posVars posCons)
            let neg = String.concat "*" (List.append negVars negCons)
            if neg.Length > 0
            then pos + "/" + neg
            elif pos.Length <= 0
            then "1"
            else pos

        override this.GetHashCode() =
            hash (this.Variables, this.Constants)

        override this.Equals(b) =
            match b with
            | :? Equation<'a, 'b> as p -> (this.Variables, this.Constants) = (p.Variables, p.Constants)
            | _ -> false

        override this.ToString() =
            if this.IsIdentity()
            then "-"
            else
                let vars = Map.map (fun k v -> $"{k}^{v}") this.Variables |> Map.toList |> List.map snd
                let cons = Map.map (fun k v -> $"{k}^{v}") this.Constants |> Map.toList |> List.map snd
                String.concat "*" (List.append vars cons)
        
        interface IComparable<Equation<'a, 'b>> with
            member this.CompareTo(other: Equation<'a, 'b>) =
                let x = compare this.Variables other.Variables
                if x = 0 then compare this.Constants other.Constants else x
        
        interface IComparable with
            member this.CompareTo(other: obj) =
                match other with
                | :? Equation<'a, 'b> ->
                    let x = compare this.Variables (unbox<Equation<'a, 'b>> other).Variables
                    if x = 0 then compare this.Constants (unbox<Equation<'a, 'b>> other).Constants else x
                | _ -> invalidArg "other" "Must be of type Equation<'a, 'b>"

    let matchEqns (fresh: FreshVars) (eqn1 : Equation<string, 'b>) (eqn2 : Equation<string, 'b>) =
        let mgu (vars : List<string>) constVars constRigids (subst : Map<int, Linear.Equation>) =
            let toTerm freshVars vars consts =
                (new Equation<string, 'b>(List.zip freshVars vars |> Map.ofList, Map.empty))
                    .Add(new Equation<string, 'b>(List.zip constVars (List.take (List.length constVars) consts) |> Map.ofList, Map.empty))
                    .Add(new Equation<string, 'b>(Map.empty, List.zip constRigids (List.skip (List.length constVars) consts) |> Map.ofList))
            let toEquation freshVars acc (var, ind) =
                match Map.tryFind ind subst with
                | Some eqn -> Map.add var (toTerm freshVars eqn.Coefficients eqn.Constants) acc
                | None -> Map.add var (new Equation<string, 'b>(freshVars.[ind])) acc
            let freshies =
                if Map.isEmpty subst
                then []
                else
                    Map.toList subst
                    |> List.head
                    |> snd
                    |> (fun (a : Linear.Equation) -> a.Coefficients)
                    |> List.length
                    |> fresh.FreshN "a"
            List.fold (toEquation freshies) Map.empty (List.mapi (fun i b -> (b, i)) vars)

        if eqn1.Variables.IsEmpty && eqn2.Variables.IsEmpty
        then
            if eqn1.Constants = eqn2.Constants
            then Some Map.empty
            else None
        elif eqn1.Variables.IsEmpty
        then None
        else
            let bases map = Map.toList map |> List.map fst
            let exponents map = Map.toList map |> List.map snd
            // put all constants on the 'constant' side of the equation, so that the matching side only has variables
            let right = eqn2.Subtract(new Equation<string, 'b>(Map.empty, eqn1.Constants))
            Linear.solve { Coefficients = exponents eqn1.Variables; Constants = List.append (exponents right.Variables) (exponents right.Constants) }
            |> Option.map (mgu (bases eqn1.Variables) (bases right.Variables) (bases right.Constants))

    let unify (fresh: FreshVars) (eqn1 : Equation<string, 'b>) (eqn2 : Equation<string, 'b>) =
        matchEqns fresh (eqn1.Add(eqn2.Invert())) (new Equation<string, 'b>())