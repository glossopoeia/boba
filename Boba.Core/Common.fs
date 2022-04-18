namespace Boba.Core

module Common =

    open System.Text

    // Maybe monad
    type MaybeBuilder() =
        member this.Bind(x, f) = 
            match x with
            | None -> None
            | Some a -> f a

        member this.Return(x) = 
            Some x
   
    let maybe = new MaybeBuilder()


    // State monad
    type Stateful<'state, 'result> =
        Stateful of ('state -> 'result * 'state)

    let run state (Stateful f) = f state

    let get = Stateful (fun state -> (state, state))
    
    let put item = Stateful (fun _ -> ((), item))

    type StateBuilder() =
        member this.Zero () = Stateful(fun s -> (), s)
        member this.Return x = Stateful(fun s -> x, s)
        member inline this.ReturnFrom (x: Stateful<'s, 'a>) = x
        member this.Bind (x, f) : Stateful<'s, 'b> =
            Stateful(fun state ->
                let (result: 'a), state = run state x
                run state (f result))
        member this.Combine (x1: Stateful<'s, 'a>, x2: Stateful<'s, 'b>) =
            Stateful(fun state ->
                let result, state = run state x1
                run state x2)
        member this.Delay f : Stateful<'s, 'a> = f ()
        member this.For (seq, (f: 'a -> Stateful<'s, 'b>)) =
            if Seq.isEmpty seq
            then this.Zero ()
            else
                seq
                |> Seq.map f
                |> Seq.reduceBack (fun x1 x2 -> this.Combine (x1, x2))
        member this.While (f, x) =
            if f () then this.Combine (x, this.While (f, x))
            else this.Zero ()
    
    let state = StateBuilder()


    // Function helpers
    let constant a _ = a

    let drop _ b = b

    let pair x y = (x, y)

    let curry f a b = f (a,b)

    let uncurry f (a,b) = f a b


    // Number helpers
    let div_floor n m =
        let q = n/m;
        let r = n%m;
        if (r > 0 && m < 0) || (r < 0 && m > 0)
        then q-1
        else q

    let modulo n m =
        let r = n%m;
        if (r > 0 && m < 0) || (r < 0 && m > 0)
        then r+m
        else r

    
    // String helpers

    /// Join a sequence of strings using a delimiter.
    /// Equivalent to String.Join() but without arrays.
    let join items (delim : string) =
        if Seq.isEmpty items
        then ""
        else

        // Collect the result in the string builder buffer
        // The end-sequence will be "item1,delim,...itemN,delim"
        let buff = 
            Seq.fold 
                (fun (buff :StringBuilder) s -> buff.Append($"{s}").Append(delim)) 
                (new StringBuilder()) 
                items

        // We don't want the last delim in the result buffer, remove
        buff.Remove(buff.Length-delim.Length, delim.Length).ToString()


    // List helpers
    let appendBack r l = List.append l r

    let append3 l c r = List.append l (List.append c r)

    let removeAt index list =
        list |> List.indexed |> List.filter (fun (i, _) -> i <> index) |> List.map snd

    let zipWith f l r = List.zip l r |> List.map f

    let listTraverseOption lopts =
        let cons h t = h :: t
        let optApply f arg =
            match f with
            | Some fp -> Option.map fp arg
            | None -> None
        let folder optElem st = 
            optApply (optApply (Some cons) optElem) st
        List.foldBack folder lopts (Some [])


    // Map helpers
    let mapKeys m = m |> Map.toSeq |> Seq.map fst |> Set.ofSeq

    let mapValues f m = Map.map (fun _ v -> f v) m

    let mapRemoveSet set m = Map.filter (fun k _ -> not (Set.contains k set)) m

    let mapUnion f l r =
        Map.fold (fun s k v ->
            match Map.tryFind k s with
            | Some v' -> Map.add k (f (v, v')) s
            | None -> Map.add k v s) l r

    /// Apply the left substitution to each element in the right substitution, then combine the
    /// two substitutions preferring the element in the left in the case of overlapping keys.
    let composeSubst subst subl subr = Map.map (fun _ v -> subst subl v) subr |> mapUnion fst subl

    let merge (l : Map<'a, 'b>) (r: Map<'a, 'b>) =
        let sharedKeys = Set.intersect (mapKeys l) (mapKeys r)
        let subsetL = Set.filter (fun k -> Set.contains k sharedKeys) (mapKeys l)
        let subsetR = Set.filter (fun k -> Set.contains k sharedKeys) (mapKeys r)
        if subsetL = subsetR
        then mapUnion fst l r |> Option.Some
        else Option.None