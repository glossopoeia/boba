namespace Boba.Core


module Basic =

    let keys m =
        Map.fold (fun l k _ -> k :: l) [] m

    let mapKeys f m =
        Map.fold (fun s k v -> Map.add (f k) v s) Map.empty m

    let mapValues f m =
        Map.map (fun _ v -> f v) m

    let mergeMap a b (f : 'a -> 'b * 'b -> 'b) =
        Map.fold (fun s k v ->
            match Map.tryFind k s with
            | Some v' -> Map.add k (f k (v, v')) s
            | None -> Map.add k v s) a b


module Abelian =

    open Basic

    /// Represents a simple Abelian equation composed of constant values and variables which can each have a signed integer exponent.
    /// The implementation uses dictionaries as a form of signed multiset, where an element in the set can have more than one occurence
    /// (represented by a positive exponent) or even negative occurences (represented by a negative exponent). If an element has exactly zero
    /// occurences, it is removed from the dictionary for efficiency.
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

        member this.ExponentOf var =
            if this.Variables.ContainsKey(var)
            then this.Variables.[var]
            else 0

        /// Determines whether all exponents in the equation are integer multiples of the given divisor.
        member this.DividesPowers divisor =
            let divides k pow = pow % divisor = 0
            Map.forall divides this.Variables && Map.forall divides this.Constants

        /// For a given variable, returns whether there is another variable in the equation that has a higher exponent.
        member this.NotMax var =
            let examined = this.ExponentOf var |> abs
            let varHasGreaterExponent k v = k <> var && abs v >= examined
            Map.exists varHasGreaterExponent this.Variables

        /// Negates each exponent in the equation.
        member this.Invert () =
            new Equation<'a, 'b>(mapValues (( ~- )) this.Variables, mapValues (( ~- )) this.Constants)

        /// Combine two Abelian unit equations. Values that appear in both equations have their exponents multiplied.
        member this.Add (other: Equation<'a, 'b>) =
            let mergeAdd k (v1, v2) = v1 + v2
            let isExponentZero _ v = v <> 0
            let vars = mergeMap this.Variables other.Variables mergeAdd |> Map.filter isExponentZero
            let constants = mergeMap this.Constants other.Constants mergeAdd |> Map.filter isExponentZero
            new Equation<'a, 'b>(vars, constants)

        /// Removes the given equation from this Abelian unit equation. Equivalent to `this.Add(other.Invert())`.
        member this.Subtract (other: Equation<'a, 'b>) = other.Invert() |> this.Add;

        /// Multiplies each exponent in the unit equation by the given factor.
        member this.Scale (factor: int) =
            let scale v = v * factor
            new Equation<'a, 'b>(mapValues scale this.Variables, mapValues scale this.Constants)

        /// Divides each exponent in the unit equation by the given factor.
        member this.Divide (factor: int) =
            let scale v = v / factor
            new Equation<'a, 'b>(mapValues scale this.Variables, mapValues scale this.Constants)

        /// Removes the specified variable from the unit, and divides all other powers by the removed variable's power.
        member this.Pivot (var: 'a) =
            let pivotPower = this.ExponentOf var
            let inverse = new Equation<'a, 'b>(var)
            this.Subtract(inverse.Scale(pivotPower))
                .Divide(pivotPower)
                .Invert();

        member this.Free () = keys this.Variables |> Set.ofList

        /// Substitutes the given unit for the specified variable, applying the variable's power to the substituted unit.
        member this.Substitute (name: 'a) (other: Equation<'a, 'b>) =
            other.Subtract(new Equation<'a, 'b>(name))
                .Scale(this.ExponentOf(name))
                .Add(this);