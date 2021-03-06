namespace Boba.Core

module Expression =

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
        | PInteger of int
        | PDecimal of float
        | PString of string
        | PChar of char
        | PBool of bool

    type FixedSizeFactor =
        | FixedConst of int
        | FixedVar of string
        | FixedFactor of factor: int * var: string
    type FixedSizeExpression = FixedExpr of List<FixedSizeFactor>

    type Word =
        | WStatementBlock of expr: Expression
        | WLetDefs of defs: List<LocalDefinition> * expr: Expression
        | WHandle of parameters: List<string> * body: Expression * handlers: List<Handler> * afterward: Expression
        | WMatch of clauses: List<MatchClause> * otherwise: Option<Expression>
        | WIf of thenClause: Expression * elseClause: Expression
        | WWhile of testClause: Expression * bodyClause: Expression
        | WFor of forClauses: List<ForClause> * breakClauses: List<BreakClause> * body: Expression
        | WFunctionLiteral of Expression
        | WTupleLiteral of fromDot: string * consumed: int
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
        | WWithState of Word
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
        | WInteger of int
        | WDecimal of float
        | WChar of char
    and Expression = List<Word>
    and LocalDefinition = { Name: string; Body: List<Word> }
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
