namespace Boba.Core

module Common =

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


    // List helpers
    let appendBack r l = List.append l r

    let append3 l c r = List.append l (List.append c r)

    let removeAt index list =
        list |> List.indexed |> List.filter (fun (i, _) -> i <> index) |> List.map snd


    // Map helpers
    let mapKeys m = m |> Map.toSeq |> Seq.map fst |> Set.ofSeq

    let mapValues f m = Map.map (fun _ v -> f v) m

    let mapUnion f l r =
        Map.fold (fun s k v ->
            match Map.tryFind k s with
            | Some v' -> Map.add k (f (v, v')) s
            | None -> Map.add k v s) l r

    let merge (l : Map<'a, 'b>) (r: Map<'a, 'b>) =
        let sharedKeys = Set.intersect (mapKeys l) (mapKeys r)
        let subsetL = Set.filter (fun k -> Set.contains k sharedKeys) (mapKeys l)
        let subsetR = Set.filter (fun k -> Set.contains k sharedKeys) (mapKeys r)
        if subsetL = subsetR
        then mapUnion fst l r |> Option.Some
        else Option.None