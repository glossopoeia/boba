namespace Boba.Compiler

module Syntax =

    open FSharp.Text.Lexing
    open Boba.Core.Types

    type IdentifierKind =
        | ISmall
        | IBig
        | IPredicate
        | IOperator

    type Identifier = { Name: string; Kind: IdentifierKind; Position: Position }

    type IntegerLiteral = { Value: string; Size: IntegerSize; Position: Position }

    type DecimalLiteral = { Value: string; Size: FloatSize; Position: Position }

    type StringLiteral = { Value: string; Position: Position }

    type RemotePath = { Org: Identifier; Project: Identifier; Unit: Identifier; Major: IntegerLiteral; Minor: IntegerLiteral; Patch: IntegerLiteral }
    
    type ImportPath =
        | IPLocal of StringLiteral
        | IPRemote of RemotePath

    type Import = { Explicit: List<Identifier>; Path: ImportPath; Alias: Identifier }



    type Declaration =
        | DFunc of Identifier


    type Pattern =
        | PInteger of IntegerLiteral
        | PDecimal of DecimalLiteral
        | PString of StringLiteral


    type Word =
        | EStatementBlock of List<Statement>
        | EIdentifier of Identifier
        | EInteger of IntegerLiteral
        | EDecimal of DecimalLiteral
        | EString of StringLiteral
    and Statement =
        | SLet of bindings: List<Pattern> * body: List<Word>
        | SLocals of defs: List<LocalFunction>
        | SExpression of body: List<Word>
    and LocalFunction = { Name: Identifier; Body: List<Word> }


    
    type Unit =
        | UMain of List<Import> * List<Declaration> * List<Word>
        | UExport of List<Import> * List<Declaration> * List<Identifier>