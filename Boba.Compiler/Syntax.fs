namespace Boba.Compiler

module Syntax =

    open FSharp.Text.Lexing
    open Boba.Core.Kinds
    open Boba.Core.Types
    open Boba.Core.DotSeq



    type NameKind =
        | ISmall
        | IBig
        | IPredicate
        | IOperator

    type Name = { Name: string; Kind: NameKind; Position: Position }

    let nameToString (n: Name) = n.Name

    let namesToStrings ns = Seq.map (fun (n: Name) -> n.Name) ns

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
        // TODO: the below construction doesn't seem rich enough for general record patterns
        | PRecord of DotSeq<(Name * Pattern)>
        | PConstructor of Identifier * DotSeq<Pattern>
        | PNamed of Name * Pattern
        | PRef of Pattern
        | PWildcard
        | PInteger of IntegerLiteral
        | PDecimal of DecimalLiteral
        | PString of StringLiteral
        | PTrue
        | PFalse

    let rec patternNames p =
        match p with
        | PNamed (name, sub) -> name :: patternNames sub

        | PTuple ps -> toList ps |> List.collect patternNames
        | PList ps -> toList ps |> List.collect patternNames
        | PVector ps -> toList ps |> List.collect patternNames
        | PSlice ps -> toList ps |> List.collect patternNames
        // TODO: this seems suspicious, might not be right (forgetting row pattern var?)
        | PRecord ps -> toList ps |> List.collect (snd >> patternNames)
        | PConstructor (_, ps) -> toList ps |> List.collect patternNames
        | PRef p -> patternNames p
        | _ -> []

    let getFlatVars pats =
        let getFlatVar pat =
            match pat with
            | PNamed (v, PWildcard) -> Some v
            | _ -> None
        toList pats
        |> List.map getFlatVar
        |> Boba.Core.Common.listTraverseOption
        |> Option.map (List.map nameToString)


    type Word =
        | EStatementBlock of List<Statement>
        | EHandle of pars: List<Name> * handled: List<Statement> * handlers: List<Handler> * ret: List<Word>
        | EInject of List<Name> * List<Statement>
        | EMatch of clauses: List<MatchClause> * otherwise: List<Word>
        | EIf of cond: List<Word> * thenClause: List<Statement> * elseClause: List<Statement>
        | EWhile of cond: List<Word> * body: List<Statement>

        | EFunctionLiteral of List<Word>
        | ETupleLiteral of rest: List<Word> * elements: List<List<Word>>
        | EListLiteral of rest: List<Word> * elements: List<List<Word>>
        | EVectorLiteral of rest: List<Word> * elements: List<List<Word>>
        | ESliceLiteral of min: List<FixedSizeTermFactor> * max: List<FixedSizeTermFactor>

        | ERecordLiteral of rest: List<Word>
        | EExtension of Name
        | ERestriction of Name
        | ESelect of dontDrop: bool * Name

        | EVariantLiteral of name: Name * value: List<Word>
        | EEmbedding of Name
        | ECase of cases: List<CaseClause> * elseClause: List<Word>

        | EWithPermission of List<Name> * List<Statement>
        | ETrust
        | EDistrust
        | EAudit

        | EWithState of List<Statement>
        | ENewRef
        | EGetRef
        | EPutRef

        | EUntag
        | EBy of Identifier
        | EPer of Identifier

        | EDo
        | EIdentifier of Identifier
        | EInteger of IntegerLiteral
        | EDecimal of DecimalLiteral
        | EString of StringLiteral
        | ETrue
        | EFalse

        // Used during type inference to implement dictionary passing, never constructed by front end
        | EMethodPlaceholder of string * Type
        | ERecursivePlaceholder of string * Type
        | EOverloadPlaceholder of Type
    and Statement =
        | SLet of MatchClause
        | SLocals of defs: List<LocalFunction>
        | SExpression of body: List<Word>
    and LocalFunction = { Name: Name; Body: List<Word> }
    and Handler = { Name: Identifier;  FixedParams: List<Name>; Params: List<Name>; Body: List<Word> }
    and MatchClause = { Matcher: DotSeq<Pattern>; Body: List<Word> }
    and CaseClause = { Tag: Name; Body: List<Word> }

    let rec wordFree word =
        match word with
        | EStatementBlock ss -> statementsFree ss
        | EHandle (ps, hdld, hdlrs, aft) ->
            let pars = namesToStrings ps |> Set.ofSeq
            let hdldFree = statementsFree hdld
            let hdlrsFree = Set.difference (Seq.collect handlerFree hdlrs |> Set.ofSeq) (Set.add "resume" pars)
            let aftFree = Set.difference (exprFree aft) pars
            Set.unionMany [hdldFree; hdlrsFree; aftFree]
        | EInject (_, ss) -> statementsFree ss
        | EMatch (cs, o) -> Set.union (exprFree o) (Set.unionMany (Seq.map matchClauseFree cs))
        | EIf (c, t, e) -> Set.unionMany [exprFree c; statementsFree t; statementsFree e]
        | EWhile (c, b) -> Set.union (exprFree c) (statementsFree b)
        | EFunctionLiteral b -> exprFree b
        | ETupleLiteral _ -> failwith "Tuple literals not yet implemented."
        | EListLiteral _ -> failwith "List literals not yet implemented."
        | EVectorLiteral _ -> failwith "Vector literals not yet implemented."
        | ESliceLiteral _ -> failwith "Slice literals not yet implemented."
        | ERecordLiteral exp -> exprFree exp
        | EVariantLiteral (_, v) -> exprFree v
        | ECase (cs, o) -> Set.union (exprFree o) (Set.unionMany (Seq.map caseClauseFree cs))
        | EWithPermission (_, ss) -> statementsFree ss
        | EWithState ss -> statementsFree ss
        // TODO: this probably needs to be concatenated with the qualifier to be the true free name
        | EBy n -> Set.singleton n.Name.Name
        // TODO: this probably needs to be concatenated with the qualifier to be the true free name
        | EPer n -> Set.singleton n.Name.Name
        // TODO: this probably needs to be concatenated with the qualifier to be the true free name
        | EIdentifier i -> Set.singleton i.Name.Name
        | _ -> Set.empty
    and exprFree expr = Set.unionMany (Seq.map wordFree expr)
    and statementsFree stmts =
        match stmts with
        | [] -> Set.empty
        | SLet { Matcher = ps; Body = b } :: ss ->
            let bodyFree = exprFree b
            let ssFree = statementsFree ss
            let patternFree = toList ps |> Seq.collect patternNames |> namesToStrings |> Set.ofSeq
            Set.union bodyFree (Set.difference ssFree patternFree)
        | SLocals _ :: ss -> failwith "Local functions not yet implemented."
        | SExpression e :: ss -> exprFree e |> Set.union (statementsFree ss)
    and handlerFree handler =
        let handlerBound = Set.ofSeq (Seq.append (namesToStrings handler.Params) (namesToStrings handler.FixedParams))
        Set.difference (exprFree handler.Body) handlerBound
    and matchClauseFree (clause: MatchClause) =
        let patNames =
            toList clause.Matcher
            |> List.collect (patternNames)
            |> List.map (fun (n: Name) -> n.Name)
            |> Set.ofList
        Set.difference (exprFree clause.Body) patNames
    and caseClauseFree clause = exprFree clause.Body

    let expandFieldSyntax fields =
        List.collect (fun (n, e) -> List.append e [EExtension n]) fields

    let rec switchClausesToIfs clauses =
        match clauses with
        | [] -> failwith $"Switch expression must have an else clause."
        | [elseC] -> EStatementBlock [SExpression elseC]
        | cond :: thenC :: rest -> EIf (cond, [SExpression thenC], [SExpression [(switchClausesToIfs rest)]])



    type SType =
        | STVar of Name
        | STDotVar of Name
        | STCon of Identifier
        | STPrim of PrimType
        | STTrue
        | STFalse
        | STAnd of SType * SType
        | STOr of SType * SType
        | STNot of SType
        | STAbelianOne
        | STExponent of SType * IntegerLiteral
        | STMultiply of SType * SType
        | STFixedConst of IntegerLiteral
        | STRowExtend
        | STRowEmpty
        | STSeq of DotSeq<SType> * Kind
        | STApp of SType * SType

    let rec stypeFree ty =
        match ty with
        | STVar v -> Set.singleton v.Name
        | STDotVar v -> Set.singleton v.Name
        | STAnd (l, r) -> Set.union (stypeFree l) (stypeFree r)
        | STOr (l, r) -> Set.union (stypeFree l) (stypeFree r)
        | STNot b -> stypeFree b
        | STExponent (b, _) -> stypeFree b
        | STMultiply (l, r) -> Set.union (stypeFree l) (stypeFree r)
        | STSeq (ts, _) -> toList ts |> List.map stypeFree |> Set.unionMany
        | STApp (l, r) -> Set.union (stypeFree l) (stypeFree r)
        | _ -> Set.empty

    let sQualType context head =
        STApp (STApp (STPrim PrQual, STApp (STPrim PrConstraintTuple, STSeq (context, KConstraint))), head)
    
    let sIdentifier qualifier name size =
        { Qualifier = qualifier; Name = name; Size = size }

    let rec appendTypeArgs ty args =
        match args with
        | [] -> ty
        | t :: ts -> STApp (appendTypeArgs ty ts, t)

    let rec dotVarToDotSeq ds =
        match ds with
        | SEnd -> SEnd
        | SInd (STDotVar v, dss) -> SDot (STVar v, dotVarToDotSeq dss)
        | SDot (STDotVar _, _) -> failwith "Got a double dotted var!"
        | SInd (t, dss) -> SInd (t, dotVarToDotSeq dss)
        | SDot (t, dss) -> SDot (t, dotVarToDotSeq dss)



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
        | DOverload of name: Name * predicate: Name * template: SType
        | DInstance of name: Name * instance: SType * body: List<Word>
        | DPropagationRule of name: Name * head: List<SType> * result: List<SType>
        | DEffect of Effect
        | DTag of typeName: Name * termName: Name
        | DTypeSynonym of name: Name * pars: List<Name> * expand: SType
        | DTest of Test
        | DLaw of Law
    and Function = { Name: Name; FixedParams: List<Name>; Body: List<Word> }
    and DataType = { Name: Name; Params: List<Name>; Constructors: List<Constructor> }
    and Constructor = { Name: Name; Components: List<SType>; Result: SType }
    and Effect = { Name: Name; Params: List<Name>; Handlers: List<HandlerTemplate> }
    and TypeAssertion = { Name: Name; Matcher: SType }
    and Test = { Name: Name; Left: List<Word>; Right: List<Word>; Kind: TestKind }
    and Law = { Name: Name; Exhaustive: bool; Pars: List<Name>; Left: List<Word>; Right: List<Word>; Kind: TestKind }
    and HandlerTemplate = { Name: Name; FixedParams: List<Name>; Type: SType }

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
        | DPropagationRule (n, _, _) -> [n]
        | DOverload (n, p, _) -> [n; p]
        | DInstance (n, _, _) -> [n]
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

    let unitSetDecls unit decls =
        match unit with
        | UMain (is, _, m) -> UMain (is, decls, m)
        | UExport (is, _, e) -> UExport (is, decls, e)

    let unitImports unit =
        match unit with
        | UMain (is, _, _) -> is
        | UExport (is, _, _) -> is

    let unitDeclNames unit = unitDecls unit |> List.collect declNames

    type Program = { Units: Map<ImportPath, Unit>; Main: Unit }