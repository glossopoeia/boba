namespace Boba.Core

module Syntax =

    open Types

    type Word =
        | WHandle of pars: List<string> * handled: Expression * handlers: List<Handler> * ret: Expression
        | WNursery of par: string * body: Expression
        | WCancellable of par: string * body: Expression
        | WInject of effs: List<string> * injected: Expression
        | WIf of thenClause: Expression * elseClause: Expression
        | WWhile of cond: Expression * body: Expression
        | WVars of vars: List<string> * body: Expression

        | WFunctionLiteral of body: Expression
        | WLetRecs of List<(string * Expression)> * expr: Expression

        | WEmptyRecord
        | WExtension of string
        | WSelect of string

        | WVariantLiteral of string
        | WCase of tag: string * thenClause: Expression * elseClause: Expression

        | WHasPermission of string
        | WRequestPermission of string

        | WDo
        | WString of string
        | WInteger of string * IntegerSize
        | WDecimal of string * FloatSize
        | WChar of char

        | WCallVar of string
        | WNativeVar of string
        | WValueVar of string
        | WOverwriteValueVar of string
        | WOperatorVar of string
        | WConstructorVar of string
        | WTestConstructorVar of string
        | WDestruct
    and Expression = List<Word>
    and Handler = { Name: string; Body: Expression }

    let rec wordFree w =
        match w with
        | WHandle (p, h, hs, r) ->
            let retFree = Set.difference (exprFree r) (Set.ofList p)
            let handlersFree = Set.difference (Set.union (Set.unionMany (List.map handlerFree hs)) retFree) (Set.ofList p)
            Set.union handlersFree (exprFree h)
        | WIf (t, e) -> Set.union (exprFree t) (exprFree e)
        | WWhile (t, e) -> Set.union (exprFree t) (exprFree e)
        | WVars (v, e) -> Set.difference (exprFree e) (Set.ofList v)
        | WFunctionLiteral b -> exprFree b
        | WLetRecs (rs, b) ->
            let rsNames = List.map fst rs |> Set.ofList
            let rsFree = Set.difference (List.map (snd >> exprFree) rs |> Set.unionMany) rsNames
            let bFree = Set.difference (exprFree b) rsNames
            Set.union rsFree bFree
        | WCase (_, t, e) -> Set.union (exprFree t) (exprFree e)
        | WValueVar n -> Set.singleton n
        | WCallVar "resume" -> Set.singleton "resume"
        | _ -> Set.empty
    and exprFree e =
        Set.unionMany (List.map wordFree e)
    and handlerFree h = exprFree h.Body