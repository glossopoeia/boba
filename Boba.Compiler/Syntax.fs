namespace Boba.Compiler

module Syntax =

    open FSharp.Text.Lexing
    open Boba.Core.Types
    open Boba.Core.DotSeq



    type NameKind =
        | ISmall
        | IBig
        | IPredicate
        | IOperator
        | ITest

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
        override this.ToString() =
            match this with
            | IPLocal sl -> sl.Value
            | IPRemote r -> $"{r.Org}.{r.Project}.{r.Unit}:{r.Major}.{r.Minor}.{r.Patch}"

    type Import = { Explicit: List<Name>; Path: ImportPath; Alias: Name }



    type Pattern =
        | PTuple of DotSeq<Pattern>
        | PList of DotSeq<Pattern>
        | PVector of DotSeq<Pattern>
        | PSlice of DotSeq<Pattern>
        | PRecord of DotSeq<(Name * Pattern)>
        | PDictionary of DotSeq<(Pattern * Pattern)>
        | PConstructor of List<Name> * DotSeq<Pattern>
        | PNamed of Name * Pattern
        | PRef of Pattern
        | PWildcard
        | PInteger of IntegerLiteral
        | PDecimal of DecimalLiteral
        | PString of StringLiteral
        | PTrue
        | PFalse


    type Word =
        | EStatementBlock of List<Statement>
        | EHandle of pars: List<Name> * handled: List<Statement> * handlers: List<Handler> * ret: List<Word>
        | EMatch of clauses: List<MatchClause> * otherwise: List<Word>
        | EIf of cond: List<Word> * thenClause: List<Statement> * elseClause: List<Statement>
        | EWhile of cond: List<Word> * body: List<Statement>

        | EFunctionLiteral of List<Word>
        | ETupleLiteral of rest: List<Word> * elements: List<List<Word>>
        | EListLiteral of rest: List<Word> * elements: List<List<Word>>
        | EVectorLiteral of rest: List<Word> * elements: List<List<Word>>
        | ESliceLiteral of min: List<FixedSizeTermFactor> * max: List<FixedSizeTermFactor>
        | EDictionaryLiteral of rest: List<Word> * elements: List<List<Word>>

        | ERecordLiteral of rest: List<Word> * extensions: List<(Name * List<Word>)>
        | EExtension of Name
        | ERestriction of Name
        | ESelect of Name

        | EVariantLiteral of name: Name * value: List<Word>
        | EEmbedding of Name
        | ECase of cases: List<CaseClause> * elseClause: List<Word>

        | EWithPermission of List<Name> * List<Statement>

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
        | ETrue
        | EFalse
    and Statement =
        | SLet of MatchClause
        | SLocals of defs: List<LocalFunction>
        | SExpression of body: List<Word>
    and LocalFunction = { Name: Name; Body: List<Word> }
    and Handler = { Name: Identifier; Params: List<Name>; Body: List<Word> }
    and MatchClause = { Matcher: DotSeq<Pattern>; Body: List<Word> }
    and CaseClause = { Tag: Name; Body: List<Word> }



    type TestKind =
        | TKIsRoughly
        | TKSatisfies
        | TKViolates
        | TKIs of List<Word>
        | TKIsNot of List<Word>

    type Declaration =
        | DFunc of Function
        | DRecFuncs of List<Function>
        | DType of DataType
        | DRecTypes of List<DataType>
        | DPattern of name: Name * pars: List<Name> * expand: Pattern
        | DCheck of TypeAssertion
        | DClass of TypeclassDefinition
        | DInstance of TypeclassInstance
        | DDeriving of name: Name * pars: List<Name> * derived: Type
        | DRule of matcher: Type * body: Type
        | DEffect of Effect
        | DTag of typeName: Name * termName: Name
        | DTypeSynonym of name: Name * pars: List<Name> * expand: Type
        | DTest of Test
        | DLaw of Law
    and Function = { Name: Name; FixedParams: List<Name>; Body: List<Word> }
    and DataType = { Name: Name; Params: List<Name>; Constructors: List<Constructor> }
    and Constructor = { Name: Name; Components: List<Type> }
    and Effect = { Name: Name; Params: List<Name>; Handlers: List<HandlerTemplate> }
    and TypeAssertion = { Name: Name; Matcher: QualifiedType }
    and TypeclassDefinition = {
        Name: Name;
        Params: List<Name>;
        Context: Type;
        FunDeps: List<FunctionalDependency>;
        Methods: List<Choice<TypeAssertion, Function>>;
        Minimal: List<List<Name>>;
        Laws: List<Law>
    }
    and TypeclassInstance = {
        Name: Name;
        Context: QualifiedType;
        Methods: List<Function>;
    }
    and FunctionalDependency = { Input: List<Name>; Output: List<Name> }
    and Test = { Name: Name; Left: List<Word>; Right: List<Word>; Kind: TestKind }
    and Law = { Name: Name; Exhaustive: bool; Pars: List<Name>; Left: List<Word>; Right: List<Word>; Kind: TestKind }
    and HandlerTemplate = { Name: Name; FixedParams: List<Name>; Type: QualifiedType }

    let methodName (m : Choice<TypeAssertion, Function>) =
        match m with
        | Choice1Of2 assertion -> assertion.Name
        | Choice2Of2 func -> func.Name

    let declNames decl =
        match decl with
        | DFunc f -> [f.Name]
        | DRecFuncs fs -> [for f in fs do yield f.Name]
        | DType t -> t.Name :: [for c in t.Constructors do yield c.Name]
        | DRecTypes ts -> List.concat [for t in ts do yield t.Name :: [for c in t.Constructors do yield c.Name]]
        | DPattern (n, ps, e) -> [n]
        | DClass c -> c.Name :: [for m in c.Methods do yield methodName m]
        | DEffect e -> e.Name :: [for o in e.Handlers do yield o.Name]
        | DTag (bigName, smallName) -> [bigName; smallName]
        | DTypeSynonym (n, ps, e) -> [n]
        | _ -> []


    
    type Unit =
        | UMain of List<Import> * List<Declaration> * List<Word>
        | UExport of List<Import> * List<Declaration> * List<Name>

    let unitDecls unit =
        match unit with
        | UMain (_, ds, _) -> ds
        | UExport (_, ds, _) -> ds

    let unitImports unit =
        match unit with
        | UMain (is, _, _) -> is
        | UExport (is, _, _) -> is

    let unitDeclNames unit = unitDecls unit |> List.collect declNames

    type Program = { Units: Map<ImportPath, Unit>; Main: Unit }