namespace Boba.Core

module Substitution =

    open Common
    open Fresh
    open Kinds
    open Types

    type TypeAndKindSubst = { Types: Map<string, Type>; Kinds: Map<string, Kind> }

    let emptySubst = { Types = Map.empty; Kinds = Map.empty }

    let addKindSubst subst v k = { subst with Kinds = Map.add v k subst.Kinds }

    let addTypeSubst subst v t = { subst with Types = Map.add v t subst.Types }

    let mkKindSubst ks = { Types = Map.empty; Kinds = ks }

    let typeSubst tys = { Types = tys; Kinds = Map.empty }

    /// Apply the left substitution to each element in the right substitution, then combine the
    /// two substitutions preferring the element in the left in the case of overlapping keys.
    let composeSubst subst subl subr = Map.map (fun _ v -> subst subl v) subr |> mapUnion fst subl

    /// Apply the given substitution to the given kind structure. Much simpler than type substitution.
    let rec kindSubst subst k =
        match k with
        | KVar v ->
            if Map.containsKey v subst.Kinds
            then subst.Kinds.[v]
            else k
        | KRow e -> krow (kindSubst subst e)
        | KSeq s -> kseq (kindSubst subst s)
        | KArrow (l, r) -> karrow (kindSubst subst l) (kindSubst subst r)
        | _ -> k

    // let rec composeKindSubst = composeSubst kindSubst

    // let mergeKindSubstExn (s1 : Map<string, Kind>) (s2 : Map<string, Kind>) =
    //     let elemAgree v =
    //         if s1.[v] = s2.[v]
    //         then true
    //         else invalidOp $"Match substitutions clashed at {v}: {s1.[v]} <> {s2.[v]}"
    //     let agree = Set.forall (fun v -> elemAgree v) (Set.intersect (mapKeys s1) (mapKeys s2))
    //     if agree
    //     then
    //         let intermediate = mapUnion fst s1 s2
    //         Map.map (fun k v -> kindSubst intermediate v) intermediate
    //     else invalidOp "Substitutions could not be merged"
    




    let zipExtendRest (ts : Type) =
        match ts with
        | TSeq (DotSeq.SInd (_, rs)) -> typeSeq rs
        | TSeq (DotSeq.SDot (_, rs)) -> typeSeq rs
        | TSeq DotSeq.SEnd -> failwith "Tried to zipExtendRest an empty sequence."
        | any -> any

    let zipExtendHeads (ts : Type) =
        match ts with
        | TSeq (DotSeq.SInd (b, _)) -> b
        | TSeq (DotSeq.SDot (b, _)) -> b
        | TSeq DotSeq.SEnd -> failwith "Tried to zipExtendHeads an empty sequence."
        | any -> any

    let rec dotOrInd (ts : DotSeq.DotSeq<Type>) =
        match ts with
        | DotSeq.SInd (TSeq (DotSeq.SDot _), _) -> DotSeq.SDot
        | DotSeq.SDot (TSeq (DotSeq.SDot _), _) -> DotSeq.SDot
        | DotSeq.SInd (_, rs) -> dotOrInd rs
        | DotSeq.SDot (_, rs) -> dotOrInd rs
        | DotSeq.SEnd -> DotSeq.SInd

    /// Given a sequence of a form like `<a, <b*>..., c>`, where `b*` does not contain any subsequences,
    /// returns a sequence of the form `<a, b*, c>`. Abstractly, if the examined sequence contains any dotted
    /// subsequences which themselves contain no subsequences, then the dotted subsequences have their elements
    /// inserted in-order into the examined sequence at the position of the dotted subsequence.
    let rec spliceDots (ts : DotSeq.DotSeq<Type>) =
        match ts with
        | DotSeq.SDot (TSeq ts, rs) ->
            if DotSeq.any isSeq ts
            then DotSeq.SDot (typeSeq ts, spliceDots rs)
            else DotSeq.append ts (spliceDots rs)
        | DotSeq.SDot (d, rs) -> DotSeq.SDot (d, spliceDots rs)
        | DotSeq.SInd (i, rs) -> DotSeq.SInd (i, spliceDots rs)
        | DotSeq.SEnd -> DotSeq.SEnd

    let rec zipExtend (ts : DotSeq.DotSeq<Type>) =
        let rec zipExtendInc ts =
            if DotSeq.any isSeq ts
            then if DotSeq.all emptySeqOrInd ts
                 then DotSeq.SEnd
                 else if DotSeq.any (fun t -> isSeq t && emptySeqOrInd t) ts
                 then failwith "zipExtend sequences were of different length."
                 else (dotOrInd ts) (typeSeq (zipExtend (DotSeq.map zipExtendHeads ts)), zipExtendInc (DotSeq.map zipExtendRest ts))
            else ts

        if DotSeq.all isSeq ts && DotSeq.anyIndInSeq ts
        then DotSeq.map (fun t -> typeSeq (getSeq t |> zipExtend)) ts
        else zipExtendInc (spliceDots ts)

    let rec fixApp (t : Type) =
        match t with
        | TApp (TSeq ls, TSeq rs) ->
            typeSeq (DotSeq.zipWith ls rs typeApp |> DotSeq.map fixApp)
        | TApp (TSeq ls, r) ->
            typeSeq (DotSeq.zipWith ls (DotSeq.map (constant r) ls) typeApp |> DotSeq.map fixApp)
        | TApp (l, TSeq rs) ->
            // special case for type constructors that take sequences as arguments: don't bubble last nested substitution sequence up!
            // instead, the constructor takes those most nested sequences as an argument
            if canApplyKind (typeKindExn l) (typeKindExn (typeSeq rs))
            then typeApp l (typeSeq rs)
            else
                try
                    typeSeq (DotSeq.zipWith (DotSeq.map (constant l) rs) rs typeApp |> DotSeq.map fixApp)
                with
                    | ex -> failwith $"Failed to apply kind {l} : {typeKindExn l} to {TSeq rs} : {typeKindExn (TSeq rs)}"
        | TApp _ -> t
        | _ -> invalidArg (nameof t) "Called fixApp on non TApp type"

    let rec fixAnd (t : Type) =
        match t with
        | TAnd (TFalse k, _) -> TFalse k
        | TAnd (_, TFalse k) -> TFalse k
        | TAnd (TTrue _, r) -> r
        | TAnd (l, TTrue _) -> l
        | TAnd (TSeq ls, TSeq rs) ->
            typeSeq (DotSeq.zipWith ls rs typeAnd |> DotSeq.map fixAnd)
        | TAnd (TSeq ls, r) ->
            typeSeq (DotSeq.zipWith ls (DotSeq.map (constant r) ls) typeAnd |> DotSeq.map fixAnd)
        | TAnd (l, TSeq rs) ->
            typeSeq (DotSeq.zipWith (DotSeq.map (constant l) rs) rs typeAnd |> DotSeq.map fixAnd)
        | TAnd _ -> t
        | _ -> invalidArg (nameof t) "Called fixAnd on non TAnd type"

    let rec fixOr (t : Type) =
        match t with
        | TOr (TTrue k, _) -> TTrue k
        | TOr (_, TTrue k) -> TTrue k
        | TOr (TFalse _, r) -> r
        | TOr (l, TFalse _) -> l
        | TOr (TSeq ls, TSeq rs) ->
            typeSeq (DotSeq.zipWith ls rs typeOr |> DotSeq.map fixOr)
        | TOr (TSeq ls, r) ->
            typeSeq (DotSeq.zipWith ls (DotSeq.map (constant r) ls) typeOr |> DotSeq.map fixOr)
        | TOr (l, TSeq rs) ->
            typeSeq (DotSeq.zipWith (DotSeq.map (constant l) rs) rs typeOr |> DotSeq.map fixOr)
        | TOr _ -> t
        | _ -> invalidArg (nameof t) "Called fixOr on non TOr type"

    let rec fixNot (t : Type) =
        match t with
        | TNot (TSeq ns) -> typeSeq (DotSeq.map typeNot ns |> DotSeq.map fixNot)
        | TNot _ -> t
        | _ -> invalidArg (nameof t) "Called fixNot on non TExponent type"

    let rec fixExp (t : Type) =
        match t with
        | TExponent (TSeq bs, n) -> typeSeq (DotSeq.map (fun b -> typeExp b n) bs |> DotSeq.map fixExp)
        | TExponent _ -> t
        | _ -> invalidArg (nameof t) "Called fixExp on non TExponent type"

    let rec fixMul (t : Type) =
        match t with
        | TMultiply (TSeq ls, TSeq rs) ->
            typeSeq (DotSeq.zipWith ls rs typeMul |> DotSeq.map fixMul)
        | TMultiply (TSeq ls, r) ->
            typeSeq (DotSeq.zipWith ls (DotSeq.map (constant r) ls) typeMul |> DotSeq.map fixMul)
        | TMultiply (l, TSeq rs) ->
            typeSeq (DotSeq.zipWith (DotSeq.map (constant l) rs) rs typeMul |> DotSeq.map fixMul)
        | TMultiply _ -> t
        | _ -> invalidArg (nameof t) "Called fixMul on non TMultiply type"

    let rec typeSubstExn fresh subst target =
        match target with
        | TWildcard k -> TWildcard (kindSubst subst k)
        | TTrue k -> TTrue (kindSubst subst k)
        | TFalse k -> TFalse (kindSubst subst k)
        | TAbelianOne k -> TAbelianOne (kindSubst subst k)
        | TRowExtend k -> TRowExtend (kindSubst subst k)
        | TEmptyRow k -> TEmptyRow (kindSubst subst k)
        | TCon (n, k) -> TCon (n, kindSubst subst k)
        | TVar (n, k) ->
            if Map.containsKey n subst.Types
            then freshenWildcards fresh subst.Types.[n]
            else TVar (n, kindSubst subst k)
        // special case for handling dotted variables inside boolean equations, necessary for allowing polymorphic sharing of tuples based
        // on the sharing status of their elements (i.e. one unique element requires whole tuple to be unique)
        | TDotVar (n, k) ->
            if Map.containsKey n subst.Types
            then
                match subst.Types.[n] with
                | TSeq _ -> lowestSequencesToDisjunctions (kindSubst subst k) subst.Types.[n]
                | TVar (v, k) -> TDotVar (v, k)
                | TFalse k -> TFalse k
                | TTrue k -> TTrue k
                | _ -> failwith $"Trying to substitute a dotted Boolean var with something unexpected: {subst.Types.[n]}"
            else TDotVar (n, kindSubst subst k)
        | TApp (l, r) ->
            let lsub = typeSubstExn fresh subst l
            TApp (lsub, typeSubstExn fresh subst r) |> fixApp
        | TSeq ts ->
            typeSeq (DotSeq.map (typeSubstExn fresh subst) ts |> zipExtend)
        | TAnd (l, r) -> TAnd (typeSubstExn fresh subst l, typeSubstExn fresh subst r) |> fixAnd
        | TOr (l, r) -> TOr (typeSubstExn fresh subst l, typeSubstExn fresh subst r) |> fixOr
        | TNot n -> TNot (typeSubstExn fresh subst n) |> fixNot
        | TExponent (b, n) -> TExponent (typeSubstExn fresh subst b, n) |> fixExp
        | TMultiply (l, r) -> TMultiply (typeSubstExn fresh subst l, typeSubstExn fresh subst r) |> fixMul
        | _ -> target

    let typeSubstSimplifyExn fresh subst ty =
        typeSubstExn fresh subst ty |> simplifyType

    // let composeSubstExn fresh = composeSubst (typeSubstSimplifyExn fresh)
    
    // let mergeSubstExn fresh (s1 : Map<string, Type>) (s2 : Map<string, Type>) =
    //     let elemAgree v =
    //         if isKindBoolean (typeKindExn s1.[v]) || isKindBoolean (typeKindExn s2.[v])
    //         // TODO: is this actually safe? Boolean matching seems to cause problems here
    //         then true
    //         elif s1.[v] = s2.[v]
    //         then true
    //         else invalidOp $"Match substitutions clashed at {v}: {s1.[v]} <> {s2.[v]}"
    //     let agree = Set.forall (fun v -> elemAgree v) (Set.intersect (mapKeys s1) (mapKeys s2))
    //     if agree
    //     then
    //         let intermediate = mapUnion fst s1 s2
    //         Map.map (fun k v -> typeSubstSimplifyExn fresh intermediate v) intermediate
    //     else invalidOp "Substitutions could not be merged"
    


    let composeSubstExn fresh subl subr =
        {
            Kinds = Map.map (fun _ k -> kindSubst subl k) subr.Kinds |> mapUnion fst subl.Kinds;
            Types = Map.map (fun _ t -> typeSubstExn fresh subl t) subr.Types |> mapUnion fst subl.Types
        }
    
    let mergeSubstExn fresh subl subr =
        let kindElemAgree v =
            if subl.Kinds.[v] = subr.Kinds.[v]
            then true
            else invalidOp $"Match substitutions clashed at {v}: {subl.Kinds.[v]} <> {subr.Kinds.[v]}"
        let agree = Set.forall (fun v -> kindElemAgree v) (Set.intersect (mapKeys subl.Kinds) (mapKeys subr.Kinds))
        if agree
        then
            let elemAgree v =
                if isKindBoolean (typeKindExn subl.Types.[v]) || isKindBoolean (typeKindExn subr.Types.[v])
                // TODO: is this actually safe? Boolean matching seems to cause problems here
                then true
                elif subl.Types.[v] = subr.Types.[v]
                then true
                else invalidOp $"Match substitutions clashed at {v}: {subl.Types.[v]} <> {subr.Types.[v]}"
            let agree = Set.forall (fun v -> elemAgree v) (Set.intersect (mapKeys subl.Types) (mapKeys subr.Types))
            if agree
            then
                let kindIntermediate = mapUnion fst subl.Kinds subr.Kinds
                let mergedKinds = Map.map (fun k v -> kindSubst { Types = Map.empty; Kinds = kindIntermediate } v) kindIntermediate
                let typeIntermediate = mapUnion fst subl.Types subr.Types
                let mergedTypes = Map.map (fun k v -> typeSubstSimplifyExn fresh { Types = typeIntermediate; Kinds = kindIntermediate } v) typeIntermediate
                {
                    Kinds = mergedKinds;
                    Types = mergedTypes
                }
            else invalidOp "Substitutions could not be merged"
        else invalidOp "Substitutions could not be merged"
    

    // Fresh types and kinds

    let freshTypeSubst (fresh: FreshVars) quantified =
        let freshies = fresh.FreshN "f" (Seq.length quantified)
        let freshVars = Seq.zip freshies (Seq.map snd quantified) |> Seq.map TVar
        Seq.zip (Seq.map fst quantified) freshVars |> Map.ofSeq

    let freshKind (fresh: FreshVars) quantified body =
        let freshies = fresh.FreshN "k" (Seq.length quantified)
        let freshVars = Seq.map KVar freshies
        let freshened = Seq.zip quantified freshVars |> Map.ofSeq
        kindSubst { Types = Map.empty; Kinds = freshened } body

    let freshTypeExn (fresh : FreshVars) quantified body =
        let freshies = fresh.FreshN "f" (Seq.length quantified)
        let freshVars = Seq.zip freshies (Seq.map snd quantified) |> Seq.map TVar
        let freshened = Seq.zip (Seq.map fst quantified) freshVars |> Map.ofSeq
        typeSubstSimplifyExn fresh { Types = freshened; Kinds = Map.empty } body

    let instantiateKinds fresh scheme = freshKind fresh scheme.Quantified scheme.Body

    let instantiateSchemeKindsExn (fresh: FreshVars) scheme =
        let freshies = fresh.FreshN "k" (Seq.length scheme.QuantifiedKinds)
        let freshVars = Seq.map KVar freshies
        let freshened = { Types = Map.empty; Kinds = Seq.zip scheme.QuantifiedKinds freshVars |> Map.ofSeq }
        {
            QuantifiedKinds = [];
            QuantifiedTypes = [for q in scheme.QuantifiedTypes -> fst q, kindSubst freshened (snd q)];
            Body = typeSubstExn fresh freshened scheme.Body
        }

    let instantiateExn fresh scheme =
        let instKindScheme = instantiateSchemeKindsExn fresh scheme
        freshTypeExn fresh instKindScheme.QuantifiedTypes instKindScheme.Body