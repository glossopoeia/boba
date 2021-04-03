namespace Boba.Core

module Expression =

    open Types

    type Pattern =
        | PNamed of name: string * pattern: Pattern
        | PCell of body: Pattern
        | PConstructor of name: string * args: List<Pattern>
        | PTuple of elements: DotSeq.DotSeq<Pattern>
        | PList of elements: DotSeq.DotSeq<Pattern>
        | PVector of elements: DotSeq.DotSeq<Pattern>
        | PSlice of elements: DotSeq.DotSeq<Pattern>
        | PRecord of elements: List<(string * Pattern)> * row: Option<string>
        | PDictionary of elements: List<(Pattern * Pattern)> * row: Option<string>
        | PWildcard
        | PInteger of string * IntegerSize
        | PDecimal of string * FloatSize
        | PString of string
        | PChar of char
        | PBool of bool

    let rec patternFree p =
        match p with
        | PNamed (n, sp) -> Set.add n (patternFree sp)
        | PCell b -> patternFree b
        | PConstructor (_, args) -> Set.unionMany (List.map patternFree args)
        | PTuple es -> DotSeq.map patternFree es |> DotSeq.toList |> Set.unionMany
        | PVector es -> DotSeq.map patternFree es |> DotSeq.toList |> Set.unionMany
        | PSlice es -> DotSeq.map patternFree es |> DotSeq.toList |> Set.unionMany
        | PRecord (es,r) ->
            match r with
            | Some s -> Set.add s (List.map (snd >> patternFree) es |> Set.unionMany)
            | None -> List.map (snd >> patternFree) es |> Set.unionMany
        | PDictionary (es,r) ->
            match r with
            | Some s -> Set.add s (List.map (fun e -> Set.union (patternFree (fst e)) (patternFree (snd e))) es |> Set.unionMany)
            | None -> List.map (fun e -> Set.union (patternFree (fst e)) (patternFree (snd e))) es |> Set.unionMany
        | _ -> Set.empty


    type FixedSizeFactor =
        | FixedConst of int
        | FixedVar of string
        | FixedFactor of factor: int * var: string
    type FixedSizeExpression = FixedExpr of List<FixedSizeFactor>

    type Word =
        | WStatementBlock of expr: Expression
        | WLetDef of def: LocalDefinition * expr: Expression
        | WRecDefs of defs: List<LocalDefinition> * expr: Expression
        | WHandle of parameters: List<string> * body: Expression * handlers: List<Handler> * afterward: Expression
        | WMatch of clauses: List<MatchClause> * otherwise: Option<Expression>
        | WVars of vars: List<string> * body: Expression
        | WIf of thenClause: Expression * elseClause: Expression
        | WWhile of testClause: Expression * bodyClause: Expression
        | WFor of forClauses: List<ForClause> * breakClauses: List<BreakClause> * body: Expression
        | WFunctionLiteral of Expression
        | WTupleLiteral of fromDot: Option<string> * consumed: int
        | WListLiteral of heads: int * fromDot: Word * tails: int
        | WVectorLiteral of heads: int * fromDot: Word * tails: int
        | WSliceLiteral of sub: Option<Word> * lower: int * higher: int
        | WDictionaryLiteral of rest: Option<Word>
        | WRecordLiteral of fields: List<string> * rest: Option<Word>
        | WExtension of string
        | WRestriction of string
        | WSelection of string
        | WVariantLiteral of string
        | WEmbedding of string
        | WCase of cases: List<CaseClause> * otherwise: Expression
        | WWithState of Expression
        | WNewRef
        | WGetRef
        | WPutRef
        | WModifyRef
        | WUntag of string
        | WIdentifier of string
        | WConstructor of string
        | WOperator of string
        | WDo
        | WString of string
        | WInteger of string * IntegerSize
        | WDecimal of string * FloatSize
        | WChar of char

        // Used during type inference to implement dictionary passing, never constructed by front end
        | WMethodPlaceholder of string * Predicate
        | WRecursivePlaceholder of Predicate
        | WOverloadPlaceholder of Predicate
    and Expression = List<Word>
    and LocalDefinition = { Name: string; Body: Expression }
    and Handler = { Name: string; Parameters: List<string>; Clause: Expression }
    and MatchClause = { Individuals: List<Pattern>; Dotted: Option<Pattern>; Body: Expression }
    and ForClause =
        | FIntroduce of name: string * body: Expression
        | FWhen of Expression
        | FLength of size: FixedSizeExpression * fill: Option<Expression>
        | FResult of Expression
        | FBreak of BreakClause
    and BreakClause =
        | BBreak of Expression
        | BFinal of Expression
    and CaseClause = { Field: string; Body: Expression }

    let rec wordFree word =
        match word with
        | WStatementBlock e -> exprFree e
        | WLetDef (d, body) -> Set.union (Set.remove d.Name (exprFree body)) (exprFree d.Body)
        | WRecDefs (ds, body) -> Set.union (Set.difference (List.map (fun (d : LocalDefinition) -> d.Name) ds |> Set.ofList) (exprFree body)) (defsFree ds)
        | WHandle (pars, body, hs, aft) ->
            Set.union
                (exprFree body)
                (Set.difference (Set.union (Set.unionMany (List.map handlerFree hs)) (exprFree aft)) (Set.ofList pars))
        | WMatch (clauses, otherwise) ->
            Set.union (List.map matchClauseFree clauses |> Set.unionMany) (Option.defaultValue Set.empty (Option.map exprFree otherwise))
        | WVars (vs, body) -> Set.difference (exprFree body) (Set.ofList vs)
        | WIf (thenCond, elseCond) -> Set.union (exprFree thenCond) (exprFree elseCond)
        | WWhile (testClause, bodyClause) -> Set.union (exprFree testClause) (exprFree bodyClause)
        | WFor _ -> failwith "Unimplemented"
        | WFunctionLiteral l -> exprFree l
        | WTupleLiteral (Some s, _) -> Set.singleton s
        | WListLiteral (_, w, _) -> wordFree w
        | WVectorLiteral (_, w, _) -> wordFree w
        | WSliceLiteral (Some w, _, _) -> wordFree w
        | WDictionaryLiteral (Some r) -> wordFree r
        | WRecordLiteral (_, Some r) -> wordFree r
        | WCase (cases, otherwise) -> Set.union (List.map (fun c -> exprFree c.Body) cases |> Set.unionMany) (exprFree otherwise)
        | WWithState w -> exprFree w
        | WIdentifier w -> Set.singleton w
        | WConstructor w -> Set.singleton w
        | WOperator w -> Set.singleton w
        | WUntag w -> Set.singleton w
        | _ -> Set.empty
    and exprFree expr =
        List.map wordFree expr |> Set.unionMany
    and defsFree defs =
        let freeWithoutDefs = List.map (fun (d : LocalDefinition) -> exprFree d.Body) defs |> Set.unionMany
        Set.difference freeWithoutDefs (List.map (fun (d : LocalDefinition) -> d.Name) defs |> Set.ofList)
    and handlerFree h =
        Set.remove h.Name (Set.difference (Set.ofList h.Parameters) (exprFree h.Clause))
    and matchClauseFree c =
        Set.difference (exprFree c.Body) (Set.union (List.map patternFree c.Individuals |> Set.unionMany) (Option.defaultValue Set.empty (Option.map patternFree c.Dotted)))