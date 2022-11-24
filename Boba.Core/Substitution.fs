namespace Boba.Core

module Substitution =

    open Common
    open Fresh
    open Kinds
    open Types

    type TypeAndKindSubst = { Types: Map<string, Type>; Kinds: Map<string, Kind> }

    /// Apply the given substitution to the given kind structure. Much simpler than type substitution.
    let rec kindSubst subst k =
        match k with
        | KVar v ->
            if Map.containsKey v subst
            then subst.[v]
            else k
        | KRow e -> krow (kindSubst subst e)
        | KSeq s -> kseq (kindSubst subst s)
        | KArrow (l, r) -> karrow (kindSubst subst l) (kindSubst subst r)
        | _ -> k

    let rec composeKindSubst = Common.composeSubst kindSubst

    let mergeKindSubstExn (s1 : Map<string, Kind>) (s2 : Map<string, Kind>) =
        let elemAgree v =
            if s1.[v] = s2.[v]
            then true
            else invalidOp $"Match substitutions clashed at {v}: {s1.[v]} <> {s2.[v]}"
        let agree = Set.forall (fun v -> elemAgree v) (Set.intersect (mapKeys s1) (mapKeys s2))
        if agree
        then
            let intermediate = mapUnion fst s1 s2
            Map.map (fun k v -> kindSubst intermediate v) intermediate
        else invalidOp "Substitutions could not be merged"

    let kindScheme q k = { Quantified = q; Body = k }

    let generalizeKind k = { Quantified = kindFree k |> Set.toList; Body = k }

    let rec typeKindSubstExn subst t =
        match t with
        | TWildcard k -> TWildcard (kindSubst subst k)
        | TVar (v, k) -> TVar (v, kindSubst subst k)
        | TDotVar (v, k) -> TDotVar (v, kindSubst subst k)
        | TCon (c, k) -> TCon (c, kindSubst subst k)

        | TTrue k -> TTrue (kindSubst subst k)
        | TFalse k -> TFalse (kindSubst subst k)
        | TAnd (l, r) -> typeAnd (typeKindSubstExn subst l) (typeKindSubstExn subst r)
        | TOr (l, r) -> typeOr (typeKindSubstExn subst l) (typeKindSubstExn subst r)
        | TNot n -> typeNot (typeKindSubstExn subst n)

        | TAbelianOne k -> TAbelianOne (kindSubst subst k)
        | TExponent (b, p) -> TExponent (typeKindSubstExn subst b, p)
        | TMultiply (l, r) -> TMultiply (typeKindSubstExn subst l, typeKindSubstExn subst r)

        | TRowExtend k -> TRowExtend (kindSubst subst k)
        | TEmptyRow k -> TEmptyRow (kindSubst subst k)

        | TSeq ts -> typeSeq (DotSeq.map (typeKindSubstExn subst) ts)
        | TApp (l, r) -> typeApp (typeKindSubstExn subst l) (typeKindSubstExn subst r)
        | _ -> t
    




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

    let rec seqToDisjunctions seq kind =
        match seq with
        | DotSeq.SEnd -> TFalse kind
        | DotSeq.SInd (e, DotSeq.SEnd) -> e
        | DotSeq.SDot (TVar (v, k), DotSeq.SEnd) -> TDotVar (v, k)
        | DotSeq.SDot (e, DotSeq.SEnd) -> e
        | DotSeq.SInd (e, ds) -> TOr (e, seqToDisjunctions ds kind)
        | DotSeq.SDot (TVar (v, k), ds) -> TOr (TDotVar (v, k), seqToDisjunctions ds kind)
        | DotSeq.SDot (e, ds) -> TOr (e, seqToDisjunctions ds kind)

    /// Helper function for converting an extended sequence to a Boolean disjunction. This is primarily useful
    /// for helping determine the sharing attribute of a tuple, which in the type of `fst` is something like
    /// `fst : (a ^ s, z ^ r ...) ^ (s or r... or t) -> a ^ s`
    let rec lowestSequencesToDisjunctions kind sub =
        match sub with
        | TSeq DotSeq.SEnd -> TFalse kind
        | TSeq ts when DotSeq.all isSeq ts -> typeSeq (DotSeq.map (lowestSequencesToDisjunctions kind) ts)
        | TSeq ts -> seqToDisjunctions ts kind
        | _ -> sub
    
    let rec freshenWildcards (fresh: FreshVars) ty =
        match ty with
        | TWildcard k -> TVar (fresh.Fresh "w", k)
        | TApp (l, r) -> TApp (freshenWildcards fresh l, freshenWildcards fresh r)
        | TSeq ts -> typeSeq (DotSeq.map (freshenWildcards fresh) ts)
        | TAnd (l, r) -> TAnd (freshenWildcards fresh l, freshenWildcards fresh r)
        | TOr (l, r) -> TOr (freshenWildcards fresh l, freshenWildcards fresh r)
        | TNot n -> TNot (freshenWildcards fresh n)
        | TExponent (b, p) -> TExponent (freshenWildcards fresh b, p)
        | TMultiply (l, r) -> TMultiply (freshenWildcards fresh l, freshenWildcards fresh r)
        | _ -> ty

    let rec typeSubstExn fresh subst target =
        match target with
        | TVar (n, _) ->
            if Map.containsKey n subst
            then freshenWildcards fresh subst.[n]
            else target
        // special case for handling dotted variables inside boolean equations, necessary for allowing polymorphic sharing of tuples based
        // on the sharing status of their elements (i.e. one unique element requires whole tuple to be unique)
        | TDotVar (n, k) ->
            if Map.containsKey n subst
            then
                match subst.[n] with
                | TSeq _ -> lowestSequencesToDisjunctions k subst.[n]
                | TVar (v, k) -> TDotVar (v, k)
                | TFalse k -> TFalse k
                | TTrue k -> TTrue k
                | _ -> failwith $"Trying to substitute a dotted Boolean var with something unexpected: {subst.[n]}"
            else target
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
        let substr = String.concat "*" (Map.toList subst |> List.map (fun (k, v) -> $"{k}->{v}"))
        //printfn $"Subbing {ty} with {substr}"
        typeSubstExn fresh subst ty |> simplifyType
    
    let typeAndKindSubstExn fresh ksub tsub ty =
        typeKindSubstExn ksub ty |> typeSubstSimplifyExn fresh tsub

    let composeSubstExn fresh = composeSubst (typeSubstSimplifyExn fresh)
    
    let mergeSubstExn fresh (s1 : Map<string, Type>) (s2 : Map<string, Type>) =
        let elemAgree v =
            if isKindBoolean (typeKindExn s1.[v]) || isKindBoolean (typeKindExn s2.[v])
            // TODO: is this actually safe? Boolean matching seems to cause problems here
            then true
            elif s1.[v] = s2.[v]
            then true
            else invalidOp $"Match substitutions clashed at {v}: {s1.[v]} <> {s2.[v]}"
        let agree = Set.forall (fun v -> elemAgree v) (Set.intersect (mapKeys s1) (mapKeys s2))
        if agree
        then
            let intermediate = mapUnion fst s1 s2
            Map.map (fun k v -> typeSubstSimplifyExn fresh intermediate v) intermediate
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
        kindSubst freshened body

    let freshTypeExn (fresh : FreshVars) quantified body =
        let freshies = fresh.FreshN "f" (Seq.length quantified)
        let freshVars = Seq.zip freshies (Seq.map snd quantified) |> Seq.map TVar
        let freshened = Seq.zip (Seq.map fst quantified) freshVars |> Map.ofSeq
        typeSubstSimplifyExn fresh freshened body

    let instantiateKinds fresh scheme = freshKind fresh scheme.Quantified scheme.Body

    let instantiateSchemeKindsExn (fresh: FreshVars) scheme =
        let freshies = fresh.FreshN "k" (Seq.length scheme.QuantifiedKinds)
        let freshVars = Seq.map KVar freshies
        let freshened = Seq.zip scheme.QuantifiedKinds freshVars |> Map.ofSeq
        {
            QuantifiedKinds = [];
            QuantifiedTypes = [for q in scheme.QuantifiedTypes -> fst q, kindSubst freshened (snd q)];
            Body = typeKindSubstExn freshened scheme.Body
        }

    let instantiateExn fresh scheme =
        let instKindScheme = instantiateSchemeKindsExn fresh scheme
        freshTypeExn fresh instKindScheme.QuantifiedTypes instKindScheme.Body