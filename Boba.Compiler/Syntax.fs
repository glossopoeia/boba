namespace Boba.Compiler

module Syntax =

    open FSharp.Text.Lexing
    open Boba.Core.Common
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

    let stringToSmallName n = { Name = n; Kind = ISmall; Position = Position.Empty }

    type IntegerLiteral = { Value: string; Size: IntegerSize; Position: Position }
    
    type DecimalLiteral = { Value: string; Size: FloatSize; Position: Position }
    
    type StringLiteral = { Value: string; Position: Position }



    type Identifier = { Qualifier: List<Name>; Name: Name; }

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
        | PRecord of List<(Name * Pattern)>
        | PConstructor of Identifier * DotSeq<Pattern>
        | PNamed of Name * Pattern
        | PRef of Pattern
        | PWildcard
        | PInteger of IntegerLiteral
        | PDecimal of DecimalLiteral
        | PString of StringLiteral
        | PTrue
        | PFalse
    
    /// Determine if a pattern is a wildcard, or equivalent to a wildcard.
    let rec isAnyMatchPattern p =
        match p with
        | PWildcard -> true
        | PNamed (_, np) -> isAnyMatchPattern np
        | _ -> false

    let rec patternNames p =
        match p with
        | PNamed (name, sub) -> name :: patternNames sub

        | PTuple ps -> toList ps |> List.collect patternNames
        | PList ps -> toList ps |> List.collect patternNames
        | PVector ps -> toList ps |> List.collect patternNames
        | PSlice ps -> toList ps |> List.collect patternNames
        | PRecord ps -> List.collect (snd >> patternNames) ps
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
        | ETupleLiteral of rest: List<Word>
        | EListLiteral of rest: List<Word> * elements: List<List<Word>>
        | EVectorLiteral of rest: List<Word> * elements: List<List<Word>>
        | ESliceLiteral of min: List<Word> * max: List<Word>

        | ERecordLiteral of rest: List<Word>
        | EExtension of Name
        | ESelect of dontDrop: bool * Name

        | EVariantLiteral of name: Name * value: List<Word>
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

        /// Used during type inference to implement dictionary passing, never constructed by front end
        | EMethodPlaceholder of string * Type
        /// Used during type inference to implement dictionary passing, never constructed by front end
        | ERecursivePlaceholder of string * Type
        /// Used during type inference to implement dictionary passing, never constructed by front end
        | EOverloadPlaceholder of Type
    and Statement =
        | SLet of MatchClause
        | SLocals of defs: List<LocalFunction>
        | SExpression of body: List<Word>
    and LocalFunction = { Name: Name; Body: List<Word> }
    and Handler = { Name: Identifier; Params: List<Name>; Body: List<Word> }
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
        | ETupleLiteral b -> exprFree b
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
        let handlerBound = Set.ofSeq (namesToStrings handler.Params)
        Set.difference (exprFree handler.Body) handlerBound
    and matchClauseFree (clause: MatchClause) =
        let patNames =
            toList clause.Matcher
            |> List.collect (patternNames)
            |> List.map (fun (n: Name) -> n.Name)
            |> Set.ofList
        Set.difference (exprFree clause.Body) patNames
    and caseClauseFree clause = exprFree clause.Body

    let combineOccurenceMaps = Boba.Core.Common.mapUnion (fun (l, r) -> l + r)

    let chooseOccurenceMap = Boba.Core.Common.mapUnion (fun (l, r) -> max l r)

    let rec exprMaxOccurences expr =
        List.map wordMaxOccurences expr
        |> List.fold combineOccurenceMaps Map.empty
    and wordMaxOccurences word =
        match word with
        | EStatementBlock ss -> stmtsMaxOccurences ss
        | EHandle (ps, hdld, hdlrs, aft) ->
            let pars = namesToStrings ps |> Set.ofSeq
            let hdldFree = stmtsMaxOccurences hdld
            let hdlrsFree = 
                Seq.map handlerMaxOccurences hdlrs
                |> Seq.fold chooseOccurenceMap Map.empty
                |> mapRemoveSet pars
                |> Map.remove "resume"
            let aftFree = mapRemoveSet pars (exprMaxOccurences aft)
            let allHdlrsFree = chooseOccurenceMap hdlrsFree aftFree
            combineOccurenceMaps hdldFree allHdlrsFree
        | EInject (_, ss) -> stmtsMaxOccurences ss
        | EIf (c, t, e) ->
            chooseOccurenceMap (stmtsMaxOccurences t) (stmtsMaxOccurences e)
            |> combineOccurenceMaps (exprMaxOccurences c)
        | EWhile (c, b) ->
            combineOccurenceMaps (exprMaxOccurences c) (stmtsMaxOccurences b)
        | EFunctionLiteral e -> exprMaxOccurences e
        | ETupleLiteral exp -> exprMaxOccurences exp
        | EListLiteral _ -> failwith "List literals not yet implemented."
        | EVectorLiteral _ -> failwith "Vector literals not yet implemented."
        | ESliceLiteral _ -> failwith "Slice literals not yet implemented."
        | ERecordLiteral exp -> exprMaxOccurences exp
        | EVariantLiteral (_, v) -> exprMaxOccurences v
        | ECase (cs, o) ->
            Seq.map caseClauseMaxOccurences cs
            |> Seq.fold chooseOccurenceMap Map.empty
            |> combineOccurenceMaps (exprMaxOccurences o)
        | EWithPermission (_, ss) -> stmtsMaxOccurences ss
        | EWithState ss -> stmtsMaxOccurences ss
        // TODO: this probably needs to be concatenated with the qualifier to be the true free name
        | EBy n -> Map.add n.Name.Name 1 Map.empty
        // TODO: this probably needs to be concatenated with the qualifier to be the true free name
        | EPer n -> Map.add n.Name.Name 1 Map.empty
        // TODO: this probably needs to be concatenated with the qualifier to be the true free name
        | EIdentifier i -> Map.add i.Name.Name 1 Map.empty
        | _ -> Map.empty
    and stmtsMaxOccurences stmts =
        match stmts with
        | [] -> Map.empty
        | SLet { Matcher = ps; Body = b } :: ss ->
            let patternFree = toList ps |> Seq.collect patternNames |> namesToStrings |> Set.ofSeq
            let restOccs = mapRemoveSet patternFree (stmtsMaxOccurences ss)
            combineOccurenceMaps (exprMaxOccurences b) restOccs
        | SLocals _ :: ss -> failwith "Local functions not yet implemented."
        | SExpression e :: ss ->
            combineOccurenceMaps (exprMaxOccurences e) (stmtsMaxOccurences ss)
    and handlerMaxOccurences hdlr =
        let handlerBound = Set.ofSeq (namesToStrings hdlr.Params)
        mapRemoveSet handlerBound (exprMaxOccurences hdlr.Body)
    and caseClauseMaxOccurences clause = exprMaxOccurences clause.Body

    let rec substituteWord subst word =
        match word with
        | EStatementBlock ss -> [EStatementBlock (substituteStatements subst ss)]
        | EHandle (ps, hdld, hdlrs, aft) ->
            let pars = namesToStrings ps |> Set.ofSeq
            let aftSub = mapRemoveSet pars subst
            let hdlrSub = Map.remove "resume" aftSub
            [EHandle (ps,
                substituteStatements subst hdld,
                List.map (substituteHandler hdlrSub) hdlrs,
                substituteExpr aftSub aft)]
        | EInject (effs, ss) -> [EInject (effs, substituteStatements subst ss)]
        | EMatch (cs, o) -> [EMatch (List.map (substituteMatchClause subst) cs, substituteExpr subst o)]
        | EIf (c, t, e) -> [EIf (substituteExpr subst c, substituteStatements subst t, substituteStatements subst e)]
        | EWhile (c, b) -> [EWhile (substituteExpr subst c, substituteStatements subst b)]
        | EFunctionLiteral b -> [EFunctionLiteral (substituteExpr subst b)]
        | ETupleLiteral b -> [ETupleLiteral (substituteExpr subst b)]
        | EListLiteral _ -> failwith "List literals not yet implemented."
        | EVectorLiteral _ -> failwith "Vector literals not yet implemented."
        | ESliceLiteral _ -> failwith "Slice literals not yet implemented."
        | ERecordLiteral exp -> [ERecordLiteral (substituteExpr subst exp)]
        | EVariantLiteral (n, v) -> [EVariantLiteral (n, substituteExpr subst v)]
        | ECase (cs, o) -> [ECase (List.map (substituteCase subst) cs, substituteExpr subst o)]
        | EWithPermission (ps, ss) -> [EWithPermission (ps, substituteStatements subst ss)]
        | EWithState ss -> [EWithState (substituteStatements subst ss)]
        | EIdentifier i ->
            if Map.containsKey i.Name.Name subst
            then subst.[i.Name.Name]
            else [EIdentifier i]
        | _ -> [word]
    and substituteExpr subst expr = List.collect (substituteWord subst) expr
    and substituteStatements subst stmts = List.map (substituteStatement subst) stmts
    and substituteStatement subst stmt =
        match stmt with
        | SLet { Matcher = ps; Body = b } ->
            let toRemove = toList ps |> Seq.collect (fun p -> patternNames p |> namesToStrings) |> Set.ofSeq
            SLet { Matcher = ps; Body = substituteExpr (mapRemoveSet toRemove subst) b }
        | SLocals _ -> failwith "Substitution for local functions not yet implemented."
        | SExpression e -> SExpression (substituteExpr subst e)
    and substituteHandler subst hdlr =
        let toRemove = namesToStrings hdlr.Params |> Set.ofSeq
        { hdlr with Body = substituteExpr (mapRemoveSet toRemove subst) hdlr.Body }
    and substituteMatchClause subst clause =
        let toRemove = toList clause.Matcher |> Seq.collect (fun p -> patternNames p |> namesToStrings) |> Set.ofSeq
        { clause with Body = substituteExpr (mapRemoveSet toRemove subst) clause.Body }
    and substituteCase subst case = { case with Body = substituteExpr subst case.Body }

    let expandFieldSyntax fields =
        List.collect (fun (n, e) -> List.append e [EExtension n]) fields
    
    let expandTupleConsSyntax elems =
        List.collect (fun e -> List.append e [EIdentifier { Qualifier = []; Name = stringToSmallName "cons-tuple" }]) elems

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
    
    let sIdentifier qualifier name =
        { Qualifier = qualifier; Name = name; }

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
        | DOverload of name: Name * predicate: Name * template: SType * bodies: List<(string * List<Word>)>
        | DInstance of name: Name * instance: SType * body: List<Word>
        | DPropagationRule of name: Name * head: List<SType> * result: List<SType>
        | DEffect of Effect
        | DTag of typeName: Name * termName: Name
        | DTypeSynonym of name: Name * pars: List<Name> * expand: SType
        | DTest of Test
        | DLaw of Law
    and Function = { Name: Name; Body: List<Word> }
    and DataType = { Name: Name; Params: List<Name>; Constructors: List<Constructor> }
    and Constructor = { Name: Name; Components: List<SType>; Result: SType }
    and Effect = { Name: Name; Params: List<Name>; Handlers: List<HandlerTemplate> }
    and TypeAssertion = { Name: Name; Matcher: SType }
    and Test = { Name: Name; Left: List<Word>; Right: List<Word>; Kind: TestKind }
    and Law = { Name: Name; Exhaustive: bool; Params: List<Name>; Left: List<Word>; Right: List<Word>; Kind: TestKind }
    and HandlerTemplate = { Name: Name; Type: SType }

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
        | DOverload (n, p, _, _) -> [n; p]
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