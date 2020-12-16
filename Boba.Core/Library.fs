namespace Boba.Core



module Kinds =

    type Kind =
        | KData
        | KEffects
        | KFields
        | KTag
        | KFixed
        | KArrow of Kind * Kind
        | KSeq of Kind

    let isDataKind k =
        match k with
        | KData -> true
        | _ -> false

    let rec prettyKind(k : Kind) =
        match k with
        | KData -> "*"
        | KEffects -> "!"
        | KFields -> "."
        | KTag -> "#"
        | KFixed -> "+"
        | KArrow(f, a) -> "(" + prettyKind f + " -> " + prettyKind a + ")"
        | KSeq(k) -> "[" + prettyKind k + "]"

    let rec maxSeq (l : Kind) (r : Kind) =
        match (l, r) with
        | (KSeq kl, KSeq kr) -> KSeq (maxSeq kl kr)
        | (KSeq kl, _) -> KSeq kl
        | (_, KSeq kr) -> KSeq kr
        | (l, r) -> if l <> r then failwith "Non-sequence types within a sequence must all have the same kind" else l


    
module Types =

    open Basic
    open Kinds

    type IndexedVar =
        | Var of name: string * indexes: List<int>

    let varName v =
        match v with
        | Var (n, _) -> n

    let varInds v =
        match v with
        | Var (_, ind) -> ind

    type DotSeq<'a> =
        | SInd of ty: 'a * rest: DotSeq<'a>
        | SDot of ty: 'a * rest: DotSeq<'a>
        | SEnd

    let rec toSeqType (ts : 'a list) =
        match ts with
        | [] -> SEnd
        | t :: ts -> SInd (t, toSeqType ts)

    type Row<'a> =
        | RowItem of item: 'a * rest: Row<'a>
        | RowVar of var: IndexedVar
        | RowEnd

    type Type =
        | TVar of var: IndexedVar * kind: Kind
        | TCon of name: string * kind: Kind
        | TApp of left: Type * right: Type
        | TTag of tag: Abelian.Equation<IndexedVar, string>
        | TFixed of fixedSize: Abelian.Equation<IndexedVar, int>
        | TFieldRow of fieldRow: Row<Field>
        | TEffectRow of effectRow: Row<Type>
        | TSeq of seq: DotSeq<Type>
    and Field = { Name: string; Type: Type }

    let isSeq t =
        match t with
        | TSeq _ -> true
        | _ -> false

    let isInd t =
        match t with
        | TSeq _ -> false
        | _ -> true

    let getSeq t =
        match t with
        | TSeq ts -> ts
        | _ -> failwith "Called getSeq on non-TSeq"

    let emptySeqOrInd (t : Type) =
        match t with
        | TSeq (SEnd) -> true
        | TSeq (_) -> false
        | _ -> true

    let rec seqLen (ts : 'a DotSeq) =
        match ts with
        | SInd (_, rs) -> 1 + seqLen rs
        | SDot (_, rs) -> 1 + seqLen rs
        | SEnd -> 0

    let rec mapSeq (f : 'a -> 'b) (ts : 'a DotSeq) =
        match ts with
        | SInd (b, rs) -> SInd (f b, mapSeq f rs)
        | SDot (b, rs) -> SDot (f b, mapSeq f rs)
        | SEnd -> SEnd

    let rec allSeq (f : 'a -> bool) (ts : 'a DotSeq) =
        match ts with
        | SInd (b, rs) -> f b && allSeq f rs
        | SDot (b, rs) -> f b && allSeq f rs
        | SEnd -> true

    let rec anySeq (f : 'a -> bool) (ts : 'a DotSeq) =
        match ts with
        | SInd (b, rs) -> f b || anySeq f rs
        | SDot (b, rs) -> f b || anySeq f rs
        | SEnd -> false

    let rec anyIndInSeq (ts : 'a DotSeq) =
        match ts with
        | SInd _ -> true
        | SEnd -> false
        | SDot (_, rs) -> anyIndInSeq rs

    let rec appSeq (ls : 'a DotSeq) (rs : 'a DotSeq) =
        match ls with
        | SEnd -> rs
        | SInd (t, sls) -> SInd (t, appSeq sls rs)
        | SDot (t, sls) -> SDot (t, appSeq sls rs)

    let rec atIndex (ind : int) (tyseq : 'a DotSeq) =
        match tyseq with
        | SInd (t, rs) -> if ind = 0 then t else atIndex (ind - 1) rs
        | SDot (t, rs) -> if ind = 0 then t else atIndex (ind - 1) rs
        | SEnd -> failwith "Tried to index an element outside the bounds of the sequence."

    let rec kind(t : Type) =
        match t with
        | TVar(_, k) -> k
        | TCon(_, k) -> k
        | TTag _ -> KTag
        | TFixed f -> KFixed
        | TFieldRow f -> fieldRowKind f
        | TEffectRow e -> effectRowKind e
        | TApp(l, r) ->
            match kind l with
            | KArrow(al, ar) -> if (al = kind r) then ar else failwith "Kind error: tried to apply type constructor to arg of wrong kind"
            | _ -> failwith "Kind error: type constructor requires arrow kind"
        | TSeq ts -> kindSeq ts |> KSeq
    and fieldRowKind row =
        match row with
        | RowItem ({ Field.Name = name; Field.Type = ty }, rest) ->
            if isDataKind (kind ty) then fieldRowKind rest else failwith "Kind error: found a field row without a data kind for a labelled type."
        | RowVar _ -> KFields
        | RowEnd -> KFields
    and effectRowKind row =
        match row with
        | RowItem (ty, rest) ->
            if isDataKind (kind ty) then effectRowKind rest else failwith "Kind error: found a field row without a data kind for a labelled type."
        | RowVar _ -> KEffects
        | RowEnd -> KEffects
    and kindSeq (ts : DotSeq<Type>)  =
        match ts with
        | SEnd -> KData // handled by the next branch, but its presence keeps the compiler from whining
        | ts when allSeq isInd ts -> KData
        | ts when anySeq isSeq ts && anySeq isInd ts -> failwith "Tried to get kind of sequence with mixed data and nested sequences."
        | ts -> mapSeq kind ts |> maxKindSeq
    and maxKindSeq (ks : DotSeq<Kind>) =
        match ks with
        | SEnd -> failwith "Called maxKindSeq on an empty sequence."
        | SInd (k, SEnd) -> k
        | SDot (k, SEnd) -> k
        | SInd (k, ks) -> maxSeq k (maxKindSeq ks)
        | SDot (k, ks) -> maxSeq k (maxKindSeq ks)

    let rec getsub (inds : int list) (sub : Type) =
        match (inds, sub) with
        | ([], s) -> s
        | ([i], TSeq s) -> atIndex i s
        | (i :: is, TSeq s) -> getsub is (atIndex i s)
        | _ -> failwith "Tried to index a non-sequence type."

    let rec zipwith (ls : DotSeq<'a>) (rs : DotSeq<'b>) (f : 'a -> 'b -> 'c) =
        match (ls, rs) with
        | (SInd (lb, ls), SInd (rb, rs)) -> SInd ((f lb rb), zipwith ls rs f)
        | (SDot (lb, ls), SDot (rb, rs)) -> SDot ((f lb rb), zipwith ls rs f)
        | (SDot (lb, ls), SInd (rb, rs)) -> SDot ((f lb rb), zipwith ls rs f)
        | (SInd (lb, ls), SDot (rb, rs)) -> SDot ((f lb rb), zipwith ls rs f)
        | (SEnd, SEnd) -> SEnd
        | _ -> failwith "Tried to zip sequences of different lengths."

    let zipExtendRest (ts : Type) =
        match ts with
        | TSeq (SInd (_, rs)) -> TSeq rs
        | TSeq (SDot (_, rs)) -> TSeq rs
        | TSeq (SEnd) -> failwith "Tried to zipExtendRest an empty sequence."
        | any -> any

    let copyVar (i : int) (v : IndexedVar) =
        match v with
        | Var (n, inds) -> Var (n, List.append inds [i])

    let rec copyAt (i : int) (t : Type) =
        match t with
        | TVar (v, k) -> TVar (copyVar i v, k)
        | TCon _ -> t
        | TTag t -> new Abelian.Equation<IndexedVar, string>(mapKeys (copyVar i) t.Variables, t.Constants) |> TTag
        | TFixed f -> new Abelian.Equation<IndexedVar, int>(mapKeys (copyVar i) f.Variables, f.Constants) |> TFixed
        | TFieldRow fs -> TFieldRow (copyFieldRow i fs)
        | TEffectRow es -> TEffectRow (copyEffectRow i es)
        | TApp (l, r) -> TApp (copyAt i l, copyAt i r)
        | TSeq ts -> mapSeq (copyAt i) ts |> TSeq
    and copyFieldRow (i : int) (r : Row<Field>) =
        match r with
        | RowItem ({ Field.Name = name; Field.Type = ty }, rs) -> RowItem ({ Name = name; Type = copyAt i ty }, copyFieldRow i rs)
        | RowVar v -> RowVar (copyVar i v)
        | RowEnd -> RowEnd
    and copyEffectRow (i : int) (r : Row<Type>) =
        match r with
        | RowItem (ty, rs) -> RowItem (copyAt i ty, copyEffectRow i rs)
        | RowVar v -> RowVar (copyVar i v)
        | RowEnd -> RowEnd

    let zipExtendHeads (i : int) (ts : Type) =
        match ts with
        | TSeq (SInd (b, _)) -> b
        | TSeq (SDot (b, _)) -> b
        | TSeq (SEnd) -> failwith "Tried to zipExtendHeads an empty sequence."
        | any -> copyAt i any

    let rec dotOrInd (ts : Type DotSeq) =
        match ts with
        | SInd (TSeq (SDot _), _) -> SDot
        | SDot (TSeq (SDot _), _) -> SDot
        | SInd (_, rs) -> dotOrInd rs
        | SDot (_, rs) -> dotOrInd rs
        | SEnd -> SInd

    let rec spliceDots (ts : DotSeq<Type>) =
        match ts with
        | SDot (TSeq ts, rs) ->
            if anySeq isSeq ts
            then SDot (TSeq ts, spliceDots rs)
            else appSeq ts (spliceDots rs)
        | SDot (d, rs) -> SDot (d, spliceDots rs)
        | SInd (i, rs) -> SInd (i, spliceDots rs)
        | SEnd -> SEnd

    let rec zipExtend (ts : Type DotSeq) =
        let rec zipExtendInc ts i =
            if anySeq isSeq ts
            then if allSeq emptySeqOrInd ts
                 then SEnd
                 else if anySeq (fun t -> isSeq t && emptySeqOrInd t) ts
                 then failwith "zipExtend sequences were of different length."
                 else (dotOrInd ts) (TSeq (zipExtend (mapSeq (zipExtendHeads i) ts)), zipExtendInc (mapSeq zipExtendRest ts) (1 + i))
            else ts

        if allSeq isSeq ts && anyIndInSeq ts
        then mapSeq (getSeq >> zipExtend >> TSeq) ts
        else zipExtendInc (spliceDots ts) 0

    let extend (t: Type) (len: int) = [ for i in 0..len-1 do yield copyAt i t ] |> toSeqType

    let rec fixApp (t : Type) =
        match t with
        | TApp (TSeq ls, TSeq rs) -> zipwith ls rs (fun l r -> TApp (l, r) |> fixApp) |> TSeq
        | TApp (TSeq ls, r) -> zipwith ls (extend r (seqLen ls)) (fun l r -> TApp (l, r) |> fixApp) |> TSeq
        | TApp (l, TSeq rs) ->
            let canApplySeq =
                match kind l with
                | KArrow (arg, _) -> arg = kind (TSeq rs)
                | _ -> false
            if canApplySeq
            then TApp (l, TSeq rs)
            else zipwith (extend l (seqLen rs)) rs (fun l r -> TApp (l, r) |> fixApp) |> TSeq
        | TApp (l, r) -> TApp (l, r)
        | _ -> failwith "Called fixApp on non TApp"

    let rec substitute (rep : Type) (target: string) (sub: Type) =
        match rep with
        | TCon _ -> rep
        | TVar (Var (n, inds), _) -> if n = target then getsub inds sub else rep
        | TApp (l,r) -> TApp (substitute l target sub, substitute r target sub) |> fixApp
        | TSeq (ts) -> mapSeq (fun t -> substitute t target sub) ts |> zipExtend |> TSeq

module Domain =

    open Kinds
    open Types

    type Identifier =
        | IdSmall of string
        | IdBig of string
        | IdOperator of string
        | IdPredicate of string
        | IdProperty of string

    type RemotePath = { Organization: string; Project: string; Unit: string; Major: int; Minor: int; Patch: int }

    type Import = { Path: Choice<string, RemotePath>; Unqualified: List<string>; Alias: Option<string> }


    


    type DataCtor = { Name: string; Components: List<Type> }

    type DataDecl = { Name: string; TypeParams: List<string>; TagParam: Option<string>; Constructors: List<DataCtor> }


    type Pattern = { Name: string; Outputs: List<string>; Aliased: PatternExpr }

    type Declaration =
        | DData of DataDecl
        | DDataRec of List<DataDecl>
        | DPattern of Pattern



    type Unit =
        | UMain of imports: List<Import> * decls: List<Declaration> * main: Expression
        | UUnit of imports: List<Import> * decls: List<Declaration> * exports: List<Identifier>
