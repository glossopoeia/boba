namespace Boba.Compiler

module Syntax =

    open FSharp.Text.Lexing
    open Boba.Core.Types



    type NameKind =
        | ISmall
        | IBig
        | IPredicate
        | IOperator

    type Name = { Name: string; Kind: NameKind; Position: Position }

    type IntegerLiteral = { Value: string; Size: IntegerSize; Position: Position }
    
    type DecimalLiteral = { Value: string; Size: FloatSize; Position: Position }
    
    type StringLiteral = { Value: string; Position: Position }



    type FixedSizeTermFactor =
        | FixVar of Name
        | FixConst of IntegerLiteral
        | FixCoeff of IntegerLiteral * Name

    type Identifier = { Qualifier: List<Name>; Name: Name; Size: Option<List<FixedSizeTermFactor>> }

    type RemotePath = { Org: Name; Project: Name; Unit: Name; Major: IntegerLiteral; Minor: IntegerLiteral; Patch: IntegerLiteral }
    
    type ImportPath =
        | IPLocal of StringLiteral
        | IPRemote of RemotePath

    type Import = { Explicit: List<Name>; Path: ImportPath; Alias: Name }



    type Declaration =
        | DFunc of Name


    type Pattern =
        | PInteger of IntegerLiteral
        | PDecimal of DecimalLiteral
        | PString of StringLiteral


    type Word =
        | EStatementBlock of List<Statement>
        | EHandle of pars: List<Name> * handled: List<Statement> * handlers: List<Handler> * ret: List<Word>

        | EExtension of Name
        | ERestriction of Name
        | ESelect of Name

        | EEmbedding of Name

        | EWithState of List<Statement>
        | ENewRef
        | EGetRef
        | EPutRef

        | EUntag of name: List<Name>

        | EDo
        | EIdentifier of Identifier
        | EInteger of IntegerLiteral
        | EDecimal of DecimalLiteral
        | EString of StringLiteral
    and Statement =
        | SLet of bindings: List<Pattern> * body: List<Word>
        | SLocals of defs: List<LocalFunction>
        | SExpression of body: List<Word>
    and LocalFunction = { Name: Name; Body: List<Word> }
    and Handler = { Name: Identifier; Params: List<Name>; Body: List<Word> }


    
    type Unit =
        | UMain of List<Import> * List<Declaration> * List<Word>
        | UExport of List<Import> * List<Declaration> * List<Name>