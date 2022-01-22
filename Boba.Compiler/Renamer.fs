namespace Boba.Compiler

/// Renaming takes aliased and imported names present in the definitions of all declarations of a unit,
/// and turns them into their fully-qualified counter parts. This allows the renaming phase to erase
/// module import and export statements, leaving only the list of top-level declarations.
module Renamer =

    open Boba.Core.Common
    open Syntax
    open UnitDependencies

    type RenamedProgram = { Declarations: List<Declaration>; Main: List<Word> }

    /// Renaming environments map short names back to their fully qualified string names.
    /// TODO: split this into two levels, one for Type names, one for Term names
    type Env = List<Map<string, string>>

    let mapToPrefix prefix ns = Seq.map (fun s -> (s, prefix)) ns

    let mapToNoPrefix ns = mapToPrefix "" ns

    let namesToFrame ns = ns |> namesToStrings |> mapToNoPrefix |> Map.ofSeq

    let namesToPrefixFrame prefix ns = ns |> namesToStrings |> (mapToPrefix prefix) |> Map.ofSeq

    let primEnv = [Primitives.allPrimWordNames |> List.append (mapKeys Primitives.primTypes |> Set.toList) |> mapToNoPrefix |> Map.ofSeq] : Env

    let toEnvKey (id : Identifier) =
        if not (List.isEmpty id.Qualifier)
        then String.concat "." (id.Qualifier |> namesToStrings)
        else id.Name.Name

    let rec namePrefixFind env search =
        match env with
        | [] -> None
        | f :: fs ->
            if Map.containsKey search f
            then Some (f.[search])
            else namePrefixFind fs search

    let pathToNamePrefix path =
        match path with
        | IPLocal s -> s.Value.Substring(1, s.Value.Length - 2) + "."
        | IPRemote r -> $"{r.Org}.{r.Project}.{r.Unit}.{r.Major}.{r.Minor}.{r.Patch}."

    let prefixName prefix (name : Name) =
        { name with Name = prefix + name.Name }

    let extendFnName prefix (fn : Function) = { fn with Name = prefixName prefix fn.Name }

    let extendIdentName prefix (id : Identifier) = { id with Name = prefixName prefix id.Name; Qualifier = [] }

    let extendEffectName prefix (eff : Effect) =
        { eff with
            Name = prefixName prefix eff.Name;
            Handlers = List.map (fun h -> { h with Name = prefixName prefix h.Name }) eff.Handlers
        }

    let dequalifyName (env : Env) (n : Name) =
        match namePrefixFind env n.Name with
        | Some pre -> prefixName pre n
        | None -> failwith $"Name '{n.Name}' not found in scope."

    let dequalifyIdent (env : Env) (id : Identifier) =
        match namePrefixFind env (toEnvKey id) with
        | Some pre -> extendIdentName pre id
        | None -> failwith $"Name '{id.Name.Name}' not found in scope."

    let importScope (program: OrganizedProgram) (import : Import) =
        let prefix = pathToNamePrefix import.Path
        let explicits = Seq.map nameToString import.Explicit
        // TODO: check that explicit names actually exist in exports in imported module
        // requires access to all imported modules, hence the unused reference to the program
        // for future use
        Map.ofList ((import.Alias.Name, prefix) :: [for e in explicits -> (e, prefix)])

    let importsScope program imports =
        Seq.map (importScope program) imports
        |> Seq.fold (mapUnion fst) Map.empty

    let extendCtorName prefix (ctor: Constructor) =
        { ctor with Name = prefixName prefix ctor.Name }

    let extendDeclName prefix decl =
        match decl with
        | DFunc fn -> DFunc (extendFnName prefix fn)
        | DRecFuncs fns -> DRecFuncs (List.map (extendFnName prefix) fns)
        | DEffect e -> DEffect (extendEffectName prefix e)
        | DTest t -> DTest { t with Name = prefixName prefix t.Name }
        | DLaw l -> DLaw { l with Name = prefixName prefix l.Name }
        | DCheck c -> DCheck { c with Name = prefixName prefix c.Name }
        | DType d -> DType { d with Name = prefixName prefix d.Name; Constructors = List.map (extendCtorName prefix) d.Constructors }
        | DRecTypes ds ->
            DRecTypes (List.map (fun d -> { d with Name = prefixName prefix d.Name; Constructors = List.map (extendCtorName prefix) d.Constructors }) ds)
        | DTag (tagTy, tagTerm) ->
            DTag (prefixName prefix tagTy, prefixName prefix tagTerm)
        | _ -> failwith $"Renaming not yet implemented for declaration '{decl}'"

    let rec extendPatternNameUses env pat =
        match pat with
        | PConstructor (ctor, args) -> PConstructor (dequalifyIdent env ctor, Boba.Core.DotSeq.map (extendPatternNameUses env) args)
        | PNamed (n, sub) -> PNamed (n, extendPatternNameUses env sub)
        | PRef p -> PRef (extendPatternNameUses env p)
        | PRecord fs -> PRecord (Boba.Core.DotSeq.map (fun (n, p) -> (n, extendPatternNameUses env p)) fs)
        | PSlice ps -> PSlice (Boba.Core.DotSeq.map (extendPatternNameUses env) ps)
        | PVector ps -> PVector (Boba.Core.DotSeq.map (extendPatternNameUses env) ps)
        | PList ps -> PList (Boba.Core.DotSeq.map (extendPatternNameUses env) ps)
        | PTuple ps -> PTuple (Boba.Core.DotSeq.map (extendPatternNameUses env) ps)
        | _ -> pat

    let rec extendWordNameUses env word =
        match word with
        | EIdentifier id -> EIdentifier (dequalifyIdent env id)
        | EBy id -> EBy (dequalifyIdent env id)
        | EPer id -> EPer (dequalifyIdent env id)
        
        | EStatementBlock sb -> EStatementBlock (extendStmtsNameUses env sb)
        | EHandle (ps, hdld, hdlrs, aft) ->
            let hParamEnv = namesToFrame ps :: env
            let hResumeEnv = Map.add "resume" "" Map.empty :: hParamEnv
            let rnHdld = extendStmtsNameUses env hdld
            let rnHdlrs = List.map (extendHandlerNameUses hResumeEnv) hdlrs
            let rnAft = extendExprNameUses hParamEnv aft
            EHandle (ps, rnHdld, rnHdlrs, rnAft)
        | EInject (effs, expr) ->
            let rnExpr = extendStmtsNameUses env expr
            let rnEffs = List.map (dequalifyName env) effs
            EInject (rnEffs, rnExpr)
        | EMatch (cs, o) ->
            let rnCs = List.map (extendMatchClauseNameUses env) cs
            let rnOther = extendExprNameUses env o
            EMatch (rnCs, rnOther)
        | EIf (c, t, e) -> EIf (extendExprNameUses env c, extendStmtsNameUses env t, extendStmtsNameUses env e)
        | EWhile (c, b) -> EWhile (extendExprNameUses env c, extendStmtsNameUses env b)
        | EFunctionLiteral b -> EFunctionLiteral (extendExprNameUses env b)
        | ETupleLiteral _ -> failwith "Renaming on tuple literals not yet implemented."
        | EListLiteral _ -> failwith "Renaming on list literals not yet implemented."
        | EVectorLiteral _ -> failwith "Renaming on vector literals not yet implemented."
        | ESliceLiteral _ -> failwith "Renaming on slice constructors not yet implemented."
        | ERecordLiteral exp -> ERecordLiteral (extendExprNameUses env exp)
        | EVariantLiteral (lbl, varVal) -> EVariantLiteral (lbl, extendExprNameUses env varVal)
        | ECase (cs, e) ->
            ECase (List.map (fun c -> { c with Body = extendExprNameUses env c.Body }) cs, extendExprNameUses env e)
        | EWithPermission (ps, stmts) -> EWithPermission (ps, extendStmtsNameUses env stmts)
        | EWithState stmts -> EWithState (extendStmtsNameUses env stmts)
        | _ -> word
    and extendExprNameUses env expr = List.map (extendWordNameUses env) expr
    and extendStmtsNameUses env stmts =
        match stmts with
        | [] -> []
        | s :: ss ->
            let newEnv, newS = extendStatementNameUses env s
            newS :: extendStmtsNameUses newEnv ss
    and extendStatementNameUses env stmt =
        match stmt with
        | SLet { Matcher = ps; Body = vals } ->
            let letNames = Boba.Core.DotSeq.toList ps |> List.collect patternNames
            let rnPats = Boba.Core.DotSeq.map (extendPatternNameUses env) ps
            (namesToFrame letNames :: env, SLet { Matcher = rnPats; Body = List.map (extendWordNameUses env) vals })
        | SLocals _ -> failwith "Renaming of local functions is not yet implemented."
        | SExpression wds -> (env, SExpression (List.map (extendWordNameUses env) wds))
    and extendHandlerNameUses env handler =
        let bodyEnv = namesToFrame handler.Params :: env
        { handler with Name = dequalifyIdent env handler.Name; Body = extendExprNameUses bodyEnv handler.Body }
    and extendMatchClauseNameUses env clause =
        let matcher = Boba.Core.DotSeq.map (extendPatternNameUses env) clause.Matcher
        let patVars =  Boba.Core.DotSeq.toList clause.Matcher |> List.collect patternNames
        let bodyEnv = namesToFrame patVars :: env
        let body = extendExprNameUses bodyEnv clause.Body
        { Matcher = matcher; Body = body }

    let rec extendTypeNameUses env ty =
        match ty with
        | STCon ident -> 
            let dequal = dequalifyIdent env ident
            if Primitives.primTypes.ContainsKey dequal.Name.Name
            then STPrim Primitives.primTypes.[dequal.Name.Name]
            else STCon dequal
        | STAnd (l, r) -> STAnd (extendTypeNameUses env l, extendTypeNameUses env r)
        | STOr (l, r) -> STOr (extendTypeNameUses env l, extendTypeNameUses env r)
        | STNot b -> STNot (extendTypeNameUses env b)
        | STExponent (l, p) -> STExponent (extendTypeNameUses env l, p)
        | STMultiply (l, r) -> STMultiply (extendTypeNameUses env l, extendTypeNameUses env r)
        | STSeq s -> STSeq (Boba.Core.DotSeq.map (extendTypeNameUses env) s)
        | STApp (l, r) -> STApp (extendTypeNameUses env l, extendTypeNameUses env r)
        | _ -> ty

    let extendPredNameUses env (p : SPredicate) =
        { p with
            SName = dequalifyIdent env p.SName;
            SArguments = List.map (extendTypeNameUses env) p.SArguments }

    let extendQualNameUses env (q : SQualifiedType) =
        { q with
            SContext = List.map (extendPredNameUses env) q.SContext;
            SHead = extendTypeNameUses env q.SHead }

    let extendFnNameUses env (fn : Function) =
        let newEnv = namesToFrame fn.FixedParams :: env
        { fn with Body = List.map (extendWordNameUses newEnv) fn.Body }

    let extendConstructorNameUses env ctorEnv (ctor : Constructor) =
        { ctor with
            Components = List.map (extendTypeNameUses env) ctor.Components
            Result = extendTypeNameUses ctorEnv ctor.Result }

    let extendDataTypeNameUses env ctorEnv (data : DataType) =
        let frame = namesToFrame data.Params
        let newEnv = frame :: env
        let ctorEnv = frame :: ctorEnv
        { data with Constructors = List.map (extendConstructorNameUses newEnv ctorEnv) data.Constructors }
    
    let extendDeclNameUses program prefix env decl =
        match decl with
        | DFunc fn ->
            let scope = Map.add fn.Name.Name prefix Map.empty
            scope, DFunc (extendFnNameUses env fn)
        | DRecFuncs fns ->
            let recScope = namesToPrefixFrame prefix (declNames decl)
            let rnFns = List.map (extendFnNameUses (recScope :: env)) fns
            recScope, DRecFuncs (rnFns)
        | DTest t ->
            let scope = Map.add t.Name.Name prefix Map.empty
            scope, DTest { t with Left = extendExprNameUses env t.Left; Right = extendExprNameUses env t.Right }
        | DLaw l ->
            let scope = Map.add l.Name.Name prefix Map.empty
            let newEnv = namesToFrame l.Pars :: env
            scope, DLaw { l with Left = extendExprNameUses newEnv l.Left; Right = extendExprNameUses newEnv l.Right }
        | DEffect e ->
            let hdlrNames = List.map (fun (h: HandlerTemplate) -> h.Name) e.Handlers
            let scope = Map.add e.Name.Name prefix (namesToPrefixFrame prefix hdlrNames)
            let extHandlers = List.map (fun (h: HandlerTemplate) -> { h with Type = extendQualNameUses (scope :: env) h.Type }) e.Handlers
            scope, DEffect { e with Handlers = extHandlers }
        | DCheck c ->
            Map.empty, DCheck { c with Matcher = extendQualNameUses env c.Matcher }
        | DType d ->
            let recScope = namesToPrefixFrame prefix [d.Name] :: env
            let scope = namesToPrefixFrame prefix (declNames decl)
            scope, DType (extendDataTypeNameUses env recScope d)
        | DRecTypes ds ->
            let recScope = namesToPrefixFrame prefix (List.map (fun (d : DataType) -> d.Name) ds) :: env
            let scope = namesToPrefixFrame prefix (declNames decl)
            scope, DRecTypes (List.map (extendDataTypeNameUses recScope recScope) ds)
        | DTag (tagTy, tagTerm) ->
            let scope = namesToPrefixFrame prefix [tagTy; tagTerm]
            scope, DTag (tagTy, tagTerm)
        | _ -> failwith $"Renaming not implemented for declaration '{decl}'"

    let rec extendDeclsNameUses program prefix env decls =
        match decls with
        | [] -> env, []
        | d :: ds ->
            let (scope, decl) = extendDeclNameUses program prefix env d
            let (finalScope, decls) = extendDeclsNameUses program prefix (scope :: env) ds
            finalScope, decl :: decls

    let extendUnitNameUses program prefix unit =
        let env = importsScope program (unitImports unit) :: primEnv
        let (extendedEnv, rnDecls) = extendDeclsNameUses program prefix env (unitDecls unit)
        let extDecls = List.map (extendDeclName prefix) rnDecls
        match unit with
        | UMain (_, _, b) -> UMain ([], extDecls, extendExprNameUses extendedEnv b)
        | UExport _ -> UExport ([], extDecls, [])

    let renameUnitDecls program (unit: PathUnit) =
        let prefix = pathToNamePrefix unit.Path
        extendUnitNameUses program prefix unit.Unit

    let isMain unit =
        match unit with
        | UMain _ -> true
        | UExport _ -> false

    let rename (program : OrganizedProgram) =
        let units = renameUnitDecls program program.Main :: List.map (renameUnitDecls program) program.Units
        let decls = List.collect unitDecls units
        let mains = List.filter isMain units
        match mains with
        | [UMain (_, _, b)] -> { Declarations = decls; Main = b }
        | [] -> failwith "No main module found"
        | _ -> failwith "More than one main module found."
