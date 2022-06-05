namespace Boba.Core

module Kinds =

    open System.Diagnostics

    type UnifyKind =
        | KUSyntactic
        | KUBoolean
        | KUAbelian
        | KURow
        | KUSequence

    /// Each type in Boba can be categorized into a specific 'Kind'.
    ///
    /// Most kinds in Boba are simple 'base' kinds, and are used to control what type of unification
    /// is used during type inference. The aggregate kinds Seq(k) and Arrow(k1,k2) are used to construct
    /// more complex kinds, like the kind of the function type constructor and the tuple type constructor.
    ///
    /// Kind equality is determined by simple syntactic equality.
    [<DebuggerDisplay("{ToString()}")>]
    type Kind =
        /// A user-defined kind that unifies via the given unification method.
        | KUser of name: string * unify: UnifyKind
        /// Builds a new kind representing a scoped row of types of a particular kind.
        | KRow of elem: Kind
        /// Builds a new kind representing a sequence of types of a particular kind.
        | KSeq of elem: Kind
        /// Builds a new kind representing a type that consumes a type of the input kind, and returns a type of the output kind.
        | KArrow of input: Kind * output: Kind
        /// For supporting polymorphic kinds.
        | KVar of name: string

        override this.ToString () =
            match this with
            | KRow k -> $"<{k}>"
            | KSeq k -> $"[{k}]"
            | KArrow (l, r) ->
                match l with
                | KArrow _ -> $"({l}) -> {r}"
                | _ -> $"{l} -> {r}"
            | KVar v -> v
            | KUser (n, _) -> n

    let primDataKind = KUser ("Data", KUSyntactic)
    let primSharingKind = KUser ("Sharing", KUBoolean)
    let primValueKind = KUser ("Value", KUSyntactic)
    let primConstraintKind = KUser ("Constraint", KUSyntactic)
    let primEffectKind = KUser ("Effect", KUSyntactic)
    let primFieldKind = KUser ("Field", KUSyntactic)
    let primPermissionKind = KUser ("Permission", KUSyntactic)
    let primTotalityKind = KUser ("Totality", KUBoolean)
    let primFixedKind = KUser ("Fixed", KUAbelian)

    let primMeasureKind = KUser ("Measure", KUAbelian)
    let primTrustKind = KUser ("Trust", KUBoolean)
    let primClearanceKind = KUser ("Clearance", KUBoolean)
    let primHeapKind = KUser ("Heap", KUSyntactic)


    let kseq elem = KSeq elem
    
    let karrow inp out = KArrow (inp, out)


    let isKindSyntactic kind =
        match kind with
        | KUser (_, KUSyntactic) -> true
        | _ -> false

    let isKindSequence kind =
        match kind with
        | KSeq _ -> true
        | KUser (_, KUSequence) -> true
        | _ -> false

    let isKindBoolean kind =
        match kind with
        | KUser (_, KUBoolean) -> true
        | _ -> false

    let isKindAbelian kind =
        match kind with
        | KUser (_, KUAbelian) -> true
        | _ -> false

    let isKindExtensibleRow kind =
        match kind with
        | KRow _ -> true
        | KUser (_, KURow) -> true
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
        | (KSeq _, _) -> Some true
        | (_, KSeq _) -> Some false
        | (l, r) when l = r -> Some true
        | _ -> None

    /// If the two kinds can be compared, returns the greater of the two. If the two kinds cannot be
    /// compared, raises an IncomparableKinds exception.
    let maxKindExn (l : Kind) (r : Kind) =
        match kindLessOrEqualThan l r with
        | Some true -> r
        | Some false -> l
        | None -> raise (IncomparableKinds (l, r))

    /// In a dotted sequence of kinds, find the greatest of all the kinds. If any two kinds cannot be
    /// compared, raise an IncomparableKinds exception. If the dotted sequence is empty, raise an invalid
    /// argument exception.
    let maxKindsExn (ks : DotSeq.DotSeq<Kind>) =
        match DotSeq.reduce maxKindExn ks with
        | None -> invalidArg "ks" "Cannot call maxKindsExn on an empty sequence."
        | Some k -> k

    /// Compute the set of free variables in the given kind.
    let rec kindFree k =
        match k with
        | KVar v -> Set.singleton v
        | KRow e -> kindFree e
        | KSeq s -> kindFree s
        | KArrow (l, r) -> Set.union (kindFree l) (kindFree r)
        | _ -> Set.empty

    /// Apply the given substitution to the given kind structure. Much simpler than type substitution.
    let rec kindSubst subst k =
        match k with
        | KVar v -> if Map.containsKey v subst then subst.[v] else k
        | KRow e -> KRow (kindSubst subst e)
        | KSeq s -> KSeq (kindSubst subst s)
        | KArrow (l, r) -> KArrow (kindSubst subst l, kindSubst subst r)
        | _ -> k

    let rec composeKindSubst = Common.composeSubst kindSubst