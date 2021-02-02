namespace Boba.Core

module Kinds =

    open System.Diagnostics

    /// Each type in Boba can be categorized into a specific 'Kind'. Kinds do not currently
    /// support polymorphism; this might be a limitation when trying to construct certain
    /// generalized adhoc function groups.
    ///
    /// Most kinds in Boba are simple 'base' kinds, and are used to control what type of unification
    /// is used during type inference. The aggregate kinds Seq(k) and Arrow(k1,k2) are used to construct
    /// more complex kinds, like the kind of the function type constructor and the tuple type constructor.
    ///
    /// Kind equality is determined by simple syntactic equality.
    [<DebuggerDisplay("{ToString()}")>]
    type Kind =
        /// The kind of data types the are composed of a data component and a sharing component.
        | KValue
        /// The standard most-common kind of types, which unify via standard unification.
        | KData
        /// The kind of 'units of measure' types, which unify via Abelian unification.
        | KUnit
        /// The kind of 'compile-time fixed size' types, which unify via Abelian unification.
        | KFixed
        /// The kind of uniqueness and linear attributes on data types, which unify via Boolean unification.
        | KSharing
        /// The kind of effect types, which can be parameterized by values, and which unify via standard unification.
        | KEffect
        /// The kind of algebraic effect row types, which unify via row unification.
        | KEffects
        /// The kind of labels in field types, which unify via syntactic unification (really just syntactic equality in Boba).
        | KField
        /// The kind of labelled field types, which unify via row unification.
        | KFields
        /// The kind of heaps that contain mutable references, which unify via standard unification.
        | KHeap
        /// Builds a new kind representing a sequence of types of a particular kind.
        | KSeq of elem: Kind
        /// Builds a new kind representing a type that consumes a type of the input kind, and returns a type of the output kind.
        | KArrow of input: Kind * output: Kind

        override this.ToString () =
            match this with
            | KValue -> "val"
            | KData -> "data"
            | KUnit -> "unit"
            | KFixed -> "fixed"
            | KSharing -> "sharing"
            | KEffect -> "effect"
            | KEffects -> "effect..."
            | KField -> "field"
            | KFields -> "field..."
            | KHeap -> "heap"
            | KSeq k -> $"[{k}]"
            | KArrow (l, r) ->
                match l with
                | KArrow _ -> $"({l}) -> {r}"
                | _ -> $"{l} -> {r}"


    let kseq elem = KSeq elem
    
    let karrow inp out = KArrow (inp, out)


    let isKindSyntactic kind =
        match kind with
        | KValue -> true
        | KData -> true
        | KEffect -> true
        | KField -> true
        | KHeap -> true
        | _ -> false

    let isKindSequence kind =
        match kind with
        | KSeq _ -> true
        | _ -> false

    let isKindBoolean kind =
        match kind with
        | KSharing -> true
        | _ -> false

    let isKindAbelian kind =
        match kind with
        | KUnit -> true
        | KFixed -> true
        | _ -> false

    let isKindExtensibleRow kind =
        match kind with
        | KEffects -> true
        | KFields -> true
        | _ -> false

        
    /// Raised when a kind is applied to an argument that does not match the arrow kind's input.
    exception KindApplyArgMismatch of Kind * Kind
    /// Raised when attempting to apply a kind that is not an arrow kind.
    exception KindApplyNotArrow of Kind * Kind
    exception IncomparableKinds of Kind * Kind

    /// Given an arrow kind (k1 -> k2), if the argument kind k3 is equal to k1, return k2.
    /// If k1 <> k3, or if arrKind is not actually an arrow kind, raises an exception.
    let applyKindExn arrKind argKind =
        match arrKind with
        | KArrow (input, output) when input = argKind -> output
        | KArrow (input, _) -> raise (KindApplyArgMismatch (input, argKind))
        | _ -> raise (KindApplyNotArrow (arrKind, argKind))

    /// Gives a partial order to kinds via sequence nesting levels. More deeply nested sequences are
    /// considered 'bigger' than less deeply nested sequences, e.g. [data] <= [[data]]. Incomparable
    /// kinds are distinct from related kinds, and this is enforced by using Option as the result container.
    /// A Some says that the kinds are related, a None says they are not (incomparable).
    let rec kindLessOrEqualThan (l : Kind) (r : Kind) =
        match (l, r) with
        | (KSeq kl, KSeq kr) -> kindLessOrEqualThan kl kr
        | (KSeq _, _) -> Option.Some true
        | (_, KSeq _) -> Option.Some false
        | (l, r) when l = r -> Option.Some true
        | _ -> Option.None

    /// If the two kinds can be compared, returns the greater of the two. If the two kinds cannot be
    /// compared, raises an IncomparableKinds exception.
    let maxKindExn (l : Kind) (r : Kind) =
        match kindLessOrEqualThan l r with
        | Option.Some true -> r
        | Option.Some false -> l
        | Option.None -> raise (IncomparableKinds (l, r))

    /// In a dotted sequence of kinds, find the greatest of all the kinds. If any two kinds cannot be
    /// compared, raise an IncomparableKinds exception. If the dotted sequence is empty, raise an invalid
    /// argument exception.
    let maxKindsExn (ks : DotSeq.DotSeq<Kind>) =
        match DotSeq.reduce maxKindExn ks with
        | Option.None -> invalidArg "ks" "Cannot call maxKindsExn on an empty sequence."
        | Option.Some k -> k