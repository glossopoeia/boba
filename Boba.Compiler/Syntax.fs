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

    let stringToBigName n = { Name = n; Kind = IBig; Position = Position.Empty }

    type IntegerLiteral = { Value: string; Size: IntegerSize; Position: Position }
    
    type DecimalLiteral = { Value: string; Size: FloatSize; Position: Position }
    
    type StringLiteral = { Value: string; Position: Position }

    type NativeCodeLine = { Line: string; Position: Position }

    type DocumentationLine = { Line: string; Position: Position }



    type Identifier = { Qualifier: List<Name>; Name: Name; }

    type RemotePath = { Org: Name; Project: Name; Unit: Name; Major: IntegerLiteral; Minor: IntegerLiteral; Patch: IntegerLiteral }
    
    type ImportPath =
        | IPLocal of StringLiteral
        | IPRemote of RemotePath
        override this.ToString() =
            match this with
            | IPLocal sl -> sl.Value
            | IPRemote r -> $"{r.Org}.{r.Project}.{r.Unit}:{r.Major}.{r.Minor}.{r.Patch}"

    type Import = { Native: bool; Explicit: List<Name>; Path: ImportPath; Alias: Name }



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

    type ForResult =
        | FForTuple
        | FForList
        | FForVector

    type Word =
        | EStatementBlock of List<Statement>
        | EHandle of pars: List<Name> * handled: List<Statement> * handlers: List<Handler> * ret: List<Word>
        | EInject of List<Name> * List<Statement>
        | EMatch of clauses: List<MatchClause> * otherwise: List<Word>
        | EIf of cond: List<Word> * thenClause: List<Statement> * elseClause: List<Statement>
        | EWhile of cond: List<Word> * body: List<Statement>

        | EForEffect of assign: List<ForAssignClause> * body: List<Statement>
        | EForComprehension of res: List<ForResult> * assign: List<ForAssignClause> * body: List<Statement>
        | EForFold of accs: List<ForFoldInit> * assign: List<ForAssignClause> * body: List<Statement>

        | EFunctionLiteral of List<Word>
        | ETupleLiteral of rest: List<Word>
        | EListLiteral of rest: List<Word>
        | EVectorLiteral of rest: List<Word> * elements: List<List<Word>>
        | ESliceLiteral of min: List<Word> * max: List<Word>

        | ERecordLiteral of rest: List<Word>
        | EExtension of Name
        | ESelect of dontDrop: bool * Name

        | EVariantLiteral of name: Name * value: List<Word>
        | ECase of cases: List<CaseClause> * elseClause: List<Word>

        | EWithPermission of List<Name> * List<Statement> * List<Statement>
        | EIfPermission of List<Name> * List<Statement> * List<Statement>
        | EForgetPermission of List<Name>

        | ETrust
        | EDistrust
        | EAudit

        | EWithState of List<Statement>

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
    and ForFoldInit = { Name: Name; Assigned: List<Word> }
    and ForAssignClause = { Name: Name; SeqType: ForResult; Assigned: List<Word> }

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
        | EForEffect (assign, b) ->
            let maxAssign = Seq.map forAssignMaxOccurences assign |> Seq.fold combineOccurenceMaps Map.empty
            let maxBody = stmtsMaxOccurences b |> mapRemoveSet (Seq.map (fun a -> a.Name.Name) assign |> Set.ofSeq)
            combineOccurenceMaps maxAssign maxBody
        | EForComprehension (_, assign, b) ->
            let maxAssign = Seq.map forAssignMaxOccurences assign |> Seq.fold combineOccurenceMaps Map.empty
            let maxBody = stmtsMaxOccurences b |> mapRemoveSet (Seq.map (fun a -> a.Name.Name) assign |> Set.ofSeq)
            combineOccurenceMaps maxAssign maxBody
        | EForFold (accs, assign, b) ->
            let maxAccs = Seq.map forInitMaxOccurences accs |> Seq.fold combineOccurenceMaps Map.empty
            let maxAssign = Seq.map forAssignMaxOccurences assign |> Seq.fold combineOccurenceMaps Map.empty
            let maxBody = stmtsMaxOccurences b |> mapRemoveSet (Seq.map (fun a -> a.Name.Name) assign |> Set.ofSeq)
            combineOccurenceMaps maxAccs (combineOccurenceMaps maxAssign maxBody)
        | EFunctionLiteral e -> exprMaxOccurences e
        | ETupleLiteral exp -> exprMaxOccurences exp
        | EListLiteral exp -> exprMaxOccurences exp
        | EVectorLiteral _ -> failwith "Vector literals not yet implemented."
        | ESliceLiteral _ -> failwith "Slice literals not yet implemented."
        | ERecordLiteral exp -> exprMaxOccurences exp
        | EVariantLiteral (_, v) -> exprMaxOccurences v
        | ECase (cs, o) ->
            Seq.map caseClauseMaxOccurences cs
            |> Seq.fold chooseOccurenceMap Map.empty
            |> combineOccurenceMaps (exprMaxOccurences o)
        | EWithPermission (_, thenSs, elseSs) ->
            chooseOccurenceMap (stmtsMaxOccurences thenSs) (stmtsMaxOccurences elseSs)
        | EIfPermission (_, thenSs, elseSs) ->
            chooseOccurenceMap (stmtsMaxOccurences thenSs) (stmtsMaxOccurences elseSs)
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
    and forAssignMaxOccurences clause = exprMaxOccurences clause.Assigned
    and forInitMaxOccurences clause = exprMaxOccurences clause.Assigned

    let wordFree word = wordMaxOccurences word |> Map.keys |> Set.ofSeq
    let exprFree expr = exprMaxOccurences expr |> Map.keys |> Set.ofSeq
    let statementsFree stmts = stmtsMaxOccurences stmts |> Map.keys |> Set.ofSeq
    let handlerFree handler = handlerMaxOccurences handler |> Map.keys |> Set.ofSeq

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
        | EListLiteral b -> [EListLiteral (substituteExpr subst b)]
        | EVectorLiteral _ -> failwith "Vector literals not yet implemented."
        | ESliceLiteral _ -> failwith "Slice literals not yet implemented."
        | ERecordLiteral exp -> [ERecordLiteral (substituteExpr subst exp)]
        | EVariantLiteral (n, v) -> [EVariantLiteral (n, substituteExpr subst v)]
        | ECase (cs, o) -> [ECase (List.map (substituteCase subst) cs, substituteExpr subst o)]
        | EWithPermission (ps, thenSs, elseSs) ->
            [EWithPermission (ps, substituteStatements subst thenSs, substituteStatements subst elseSs)]
        | EIfPermission (ps, thenSs, elseSs) ->
            [EIfPermission (ps, substituteStatements subst thenSs, substituteStatements subst elseSs)]
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
    
    let expandListConsSyntax elems =
        List.collect (fun e -> List.append e [EIdentifier { Qualifier = []; Name = stringToSmallName "cons-list" }]) elems

    let rec switchClausesToIfs clauses =
        match clauses with
        | [] -> failwith $"Switch expression must have an else clause."
        | [elseC] -> EStatementBlock [SExpression elseC]
        | cond :: thenC :: rest -> EIf (cond, [SExpression thenC], [SExpression [(switchClausesToIfs rest)]])



    type SKind =
        | SKBase of Identifier
        | SKSeq of SKind
        | SKRow of SKind
        | SKArrow of SKind * SKind
        | SKWildcard

    type SType =
        | STWildcard
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
    
    type SConstraint =
        | SCPredicate of SType
        | SCEquality of SType * SType

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
        STApp (STApp (STPrim PrQual, STApp (STPrim PrConstraintTuple, STSeq (context, primConstraintKind))), head)
    
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

    type Native = { Name: Name; Docs: List<DocumentationLine>; Type: SType; Lines: List<NativeCodeLine> }

    type Declaration =
        | DFunc of Function
        | DRecFuncs of List<Function>
        | DNative of Native
        | DKind of UserKind
        | DType of DataType
        | DRecTypes of List<DataType>
        | DPattern of name: Name * pars: List<Name> * expand: Pattern
        | DCheck of TypeAssertion
        | DOverload of Overload
        | DInstance of Instance
        | DPropagationRule of name: Name * head: List<SType> * result: List<SConstraint>
        | DEffect of Effect
        | DTag of typeName: Name * termName: Name
        | DTypeSynonym of name: Name * pars: List<Name> * expand: SType
        | DTest of Test
        | DLaw of Law
    and Function = { Name: Name; Docs: List<DocumentationLine>; Body: List<Word> }
    and UserKind = { Name: Name; Docs: List<DocumentationLine>; Unify: UnifyKind }
    and DataType = { Name: Name; Params: List<Name * SKind>; Docs: List<DocumentationLine>; Constructors: List<Constructor>; Kind: SKind }
    and Constructor = { Name: Name; Docs: List<DocumentationLine>; Components: List<SType>; Result: SType }
    and Overload = { Name: Name; Docs: List<DocumentationLine>; Predicate: Name; Template: SType; Bodies: List<(string * List<Word>)>; Params: List<(Name*SKind)> }
    and Instance = { Name: Name; Context: DotSeq<SType>; Heads: List<SType>; Body: List<Word> }
    and Effect = { Name: Name; Docs: List<DocumentationLine>; Params: List<Name>; Handlers: List<HandlerTemplate> }
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
        | DNative n -> [n.Name]
        | DKind k -> [k.Name]
        | DType t -> t.Name :: [for c in t.Constructors do yield c.Name]
        | DRecTypes ts -> List.concat [for t in ts do yield t.Name :: [for c in t.Constructors do yield c.Name]]
        | DPattern (n, ps, e) -> [n]
        | DPropagationRule (n, _, _) -> [n]
        | DOverload o -> [o.Name; o.Predicate]
        | DInstance i -> [i.Name]
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

    type Program = { Prims: List<Unit>; Units: Map<ImportPath, Unit>; Main: Unit }