namespace Boba.Core

module DotSeq =

    open System.Diagnostics

    /// Represents a sequence in which any number of elements can be 'dotted'. Dots represent
    /// elements that can be expanded into more elements of the sequence, usually via substitution.
    [<DebuggerDisplay("{ToString()}")>]
    type DotSeq<'a> =
        | SInd of ty: 'a * rest: DotSeq<'a>
        | SDot of ty: 'a * rest: DotSeq<'a>
        | SEnd

        override this.ToString () =
            match this with
            | SInd (t, SEnd) -> $"{t}"
            | SInd (t, ts) -> $"{t},{ts}"
            | SDot (t, SEnd) -> $"{t}..."
            | SDot (t, ts) -> $"{t}...,{ts}"
            | SEnd -> ""

    /// Conses the given element onto the front of the sequence as an individual element.
    let ind elem seq = SInd (elem, seq)
    
    /// Conses the given element onto the front of the sequence as a dotted element.
    let dot elem seq = SDot (elem, seq)

    /// Create a sequence of non-dotted elements from a standard list.
    let rec ofList (ts : 'a list) =
        match ts with
        | [] -> SEnd
        | t :: ts -> ind t (ofList ts)

    /// Convert the sequence to a standard list, erasing the dots along the way.
    let rec toList (ts : DotSeq<'a>) =
        match ts with
        | SInd (i, rs) -> i :: toList rs
        | SDot (i, rs) -> i :: toList rs
        | SEnd -> []

    /// Get the length of the sequence. Dotted elements still count as one.
    let rec length (ts : 'a DotSeq) =
        match ts with
        | SInd (_, rs) -> 1 + length rs
        | SDot (_, rs) -> 1 + length rs
        | SEnd -> 0

    /// Apply a function uniformly over the elements in the sequence.
    let rec map (f : 'a -> 'b) (ts : 'a DotSeq) =
        match ts with
        | SInd (b, rs) -> ind (f b) (map f rs)
        | SDot (b, rs) -> dot (f b) (map f rs)
        | SEnd -> SEnd

    /// Determine if all the elements in the sequence pass the given predicate.
    let rec all (f : 'a -> bool) (ts : 'a DotSeq) =
        match ts with
        | SInd (b, rs) -> f b && all f rs
        | SDot (b, rs) -> f b && all f rs
        | SEnd -> true

    /// Determine if at least one element in the sequence passes the given predicate.
    let rec any (f : 'a -> bool) (ts : 'a DotSeq) =
        match ts with
        | SInd (b, rs) -> f b || any f rs
        | SDot (b, rs) -> f b || any f rs
        | SEnd -> false

    /// Whether the sequence contains any non-dotted elements.
    let rec anyIndInSeq (ts : 'a DotSeq) =
        match ts with
        | SInd _ -> true
        | SEnd -> false
        | SDot (_, rs) -> anyIndInSeq rs

    /// Join two DotSeqs together, such that the first element in rs follows the last element in ls.
    let rec append (ls : 'a DotSeq) (rs : 'a DotSeq) =
        match ls with
        | SEnd -> rs
        | SInd (t, sls) -> ind t (append sls rs)
        | SDot (t, sls) -> dot t (append sls rs)

    /// Retrieve the element at index ind in the given sequence. None if the index is outside the
    /// bounds of the sequence.
    let rec at (ind : int) (seq : 'a DotSeq) =
        match seq with
        | SInd (t, rs) -> if ind = 0 then Option.Some t else at (ind - 1) rs
        | SDot (t, rs) -> if ind = 0 then Option.Some t else at (ind - 1) rs
        | SEnd -> Option.None

    /// Combine two DotSeqs into one, using the given function as the joining operation.
    /// None if the given sequences are of different lengths.
    let rec zipwith (ls : 'a DotSeq) (rs : 'b DotSeq) (f : 'a -> 'b -> 'c) =
        match (ls, rs) with
        | (SInd (lb, ls), SInd (rb, rs)) -> zipwith ls rs f |> Option.map (ind (f lb rb))
        | (SDot (lb, ls), SDot (rb, rs)) -> zipwith ls rs f |> Option.map (dot (f lb rb))
        | (SDot (lb, ls), SInd (rb, rs)) -> zipwith ls rs f |> Option.map (dot (f lb rb))
        | (SInd (lb, ls), SDot (rb, rs)) -> zipwith ls rs f |> Option.map (dot (f lb rb))
        | (SEnd, SEnd) -> Option.Some SEnd
        | _ -> Option.None