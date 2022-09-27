namespace Boba.Compiler

/// Renaming takes aliased and imported names present in the definitions of all declarations of a unit,
/// and turns them into their fully-qualified counter parts. This allows the renaming phase to erase
/// module import and export statements, leaving only the list of top-level declarations.
module Renamer =

    open Boba.Core.Common
    open Boba.Core.Kinds
    open Syntax
    open UnitDependencies

    type NativeSubset = { UnitName: string; Imports: List<ImportPath>; Natives: List<Name> }
    
    type RenamedProgram = { Natives: List<NativeSubset>; Declarations: List<Declaration>; Main: List<Word> }

    /// Renaming environments map short names back to their fully qualified string names.
    type Env = {
        Aliases: Map<string, Map<string, string>>
        Names: Map<string, string>
        Examining: string
    }

    let mapToPrefix prefix ns = Seq.map (fun s -> (s, prefix)) ns

    let mapToNoPrefix ns = mapToPrefix "" ns

    let namesToFrame ns = ns |> namesToStrings |> mapToNoPrefix |> Map.ofSeq

    let namesToPrefixFrame prefix ns = ns |> namesToStrings |> mapToPrefix prefix |> Map.ofSeq

    let pathToNamePrefix path =
        match path with
        | IPLocal s -> s.Value.Substring(1, s.Value.Length - 2) + "."
        | IPRemote r -> $"{r.Org.Name}.{r.Project.Name}.{r.Unit.Name}.{r.Major.Value}.{r.Minor.Value}.{r.Patch.Value}."

    let prefixName prefix (name : Name) =
        { name with Name = prefix + name.Name }

    let extendFnName prefix (fn : Function) = { fn with Name = prefixName prefix fn.Name }

    let extendNativeName prefix (nat : Native) = { nat with Name = prefixName prefix nat.Name }

    let extendEffectName prefix (eff : Effect) =
        { eff with
            Name = prefixName prefix eff.Name;
            Handlers = List.map (fun h -> { h with Name = prefixName prefix h.Name }) eff.Handlers
        }

    let dequalifyUnaliased (env: Env) name =
        if Map.containsKey name env.Names
        then env.Names[name] + name
        else failwith $"Name '{name}' not found in scope in {env.Examining}."
    
    let dequalifyAliased (env : Env) alias name =
        if Map.containsKey alias env.Aliases
        then
            let exported = env.Aliases[alias]
            if Map.containsKey name exported
            then exported[name] + name
            else failwith $"Name '{name}' not found in aliased import '{alias}' in {env.Examining}"
        else failwith $"Alias '{alias}' not found in import list in {env.Examining}."
    
    let dequalifyIdent (env : Env) (id : Identifier) =
        if List.isEmpty id.Qualifier
        then { id with Qualifier = []; Name = { id.Name with Name = dequalifyUnaliased env id.Name.Name } }
        else { id with Qualifier = []; Name = { id.Name with Name = dequalifyAliased env id.Qualifier[0].Name id.Name.Name } }
    
    let findImportByAlias unit (alias: Name) =
        unitImports unit
        |> List.find (fun (i: Import) -> i.Alias.Name = alias.Name)

    let rec fullExportMap (program: OrganizedProgram) path unit =
        let exports = unitExportNames unit |> mapToPrefix (pathToNamePrefix path) |> Map.ofSeq
        let reExports = unitReExports unit |> Seq.map (reExportMap program unit) |> Seq.fold (mapUnion snd) Map.empty
        mapUnion snd reExports exports
    and reExportMap (program: OrganizedProgram) unit (rexp: ReExports) =
        let imp = findImportByAlias unit rexp.Alias
        match rexp.Exports with
        | IUAll -> fullExportMap program imp.Path (findUnit program imp.Path)
        | IUSubset es ->
            // TODO: inefficient! do this directly by just looking for the declaring unit of the re-exported name
            let ns = namesToStrings es
            fullExportMap program imp.Path (findUnit program imp.Path)
            |> Map.filter (fun k v -> Seq.contains k ns)
    
    let addImportScope (program: OrganizedProgram) (env: Env) (import: Import) =
        if import.Native
        then env
        else
            let importUnit = findUnit program import.Path
            let fullExp = fullExportMap program import.Path importUnit
            match import.Unaliased with
            | IUAll ->
                { env with
                    Aliases = Map.add import.Alias.Name fullExp env.Aliases
                    Names = mapUnion snd env.Names fullExp }
            | IUSubset es ->
                let ns = namesToStrings es
                let subset = Map.filter (fun k v -> Seq.contains k ns) fullExp
                { env with
                    Aliases = Map.add import.Alias.Name fullExp env.Aliases
                    Names = mapUnion snd env.Names subset }
    
    let addLocalName (env: Env) (n: Name) =
        { env with Names = Map.add n.Name "" env.Names }

    let addPrefixName (env: Env) (n, s) =
        { env with Names = Map.add n s env.Names }

    let addLocalNames (env: Env) ns =
        Seq.fold addLocalName env ns
    
    let addPrefixNames (env: Env) ns =
        Map.fold (fun e k v -> addPrefixName e (k, v)) env ns
    
    let importsScope program env imports =
        Seq.fold (addImportScope program) env imports

    let extendCtorName prefix (ctor: Constructor) =
        { ctor with Name = prefixName prefix ctor.Name }

    let extendDeclName prefix decl =
        match decl with
        | DFunc fn -> DFunc (extendFnName prefix fn)
        | DRecFuncs fns -> DRecFuncs (List.map (extendFnName prefix) fns)
        | DNative nat -> DNative (extendNativeName prefix nat)
        | DEffect e -> DEffect (extendEffectName prefix e)
        | DTest t -> DTest { t with Name = prefixName prefix t.Name }
        | DLaw l -> DLaw { l with Name = prefixName prefix l.Name }
        | DCheck c -> DCheck { c with Name = prefixName prefix c.Name }
        | DKind k -> DKind { k with Name = prefixName prefix k.Name }
        | DType d -> DType { d with Name = prefixName prefix d.Name; Constructors = List.map (extendCtorName prefix) d.Constructors }
        | DRecTypes ds ->
            DRecTypes (List.map (fun d -> { d with Name = prefixName prefix d.Name; Constructors = List.map (extendCtorName prefix) d.Constructors }) ds)
        | DOverload o -> DOverload { o with Name = prefixName prefix o.Name; Predicate = prefixName prefix o.Predicate }
        | DInstance i -> DInstance i
        | DPropagationRule r -> DPropagationRule { r with Name = prefixName prefix r.Name }
        | DClass c -> DClass { c with Name = prefixName prefix c.Name }
        | DTag t ->
            DTag { t with TypeName = prefixName prefix t.TypeName; TermName = prefixName prefix t.TermName }
        | DPattern p -> DPattern { p with Name = prefixName prefix p.Name }
        | DTypeSynonym s -> DTypeSynonym { s with Name = prefixName prefix s.Name }
        | _ -> failwith $"Renaming not yet implemented for declaration '{decl}'"

    let rec extendPatternNameUses env pat =
        match pat with
        | PConstructor (ctor, args) -> PConstructor (dequalifyIdent env ctor, Boba.Core.DotSeq.map (extendPatternNameUses env) args)
        | PNamed (n, sub) -> PNamed (n, extendPatternNameUses env sub)
        | PRef p -> PRef (extendPatternNameUses env p)
        | PRecord fs -> PRecord (List.map (fun (n, p) -> (n, extendPatternNameUses env p)) fs)
        | PSlice ps -> PSlice (Boba.Core.DotSeq.map (extendPatternNameUses env) ps)
        | PVector ps -> PVector (Boba.Core.DotSeq.map (extendPatternNameUses env) ps)
        | PList ps -> PList (Boba.Core.DotSeq.map (extendPatternNameUses env) ps)
        | PTuple ps -> PTuple (Boba.Core.DotSeq.map (extendPatternNameUses env) ps)
        | _ -> pat

    let rec extendWordNameUses env word =
        match word with
        | EIdentifier id -> EIdentifier (dequalifyIdent env id)
        | ETags (lIds, rIds) -> ETags (List.map (dequalifyIdent env) lIds, List.map (dequalifyIdent env) rIds)
        
        | EStatementBlock sb -> EStatementBlock (extendStmtsNameUses env sb)
        | ENursery (n, ss) ->
            let nParamEnv = addLocalName env n
            ENursery (n, extendStmtsNameUses nParamEnv ss)
        | ECancellable (n, ss) ->
            let nParamEnv = addLocalName env n
            ECancellable (n, extendStmtsNameUses nParamEnv ss)
        | EHandle (ps, hdld, hdlrs, aft) ->
            let hParamEnv = addLocalNames env ps
            let hResumeEnv = addLocalName hParamEnv (stringToSmallName "resume")
            let rnHdld = extendStmtsNameUses env hdld
            let rnHdlrs = List.map (extendHandlerNameUses hResumeEnv) hdlrs
            let rnAft = extendExprNameUses hParamEnv aft
            EHandle (ps, rnHdld, rnHdlrs, rnAft)
        | EInject (effs, expr) ->
            let rnExpr = extendStmtsNameUses env expr
            let rnEffs = List.map (dequalifyIdent env) effs
            EInject (rnEffs, rnExpr)
        | EMatch (cs, o) ->
            let rnCs = List.map (extendMatchClauseNameUses env) cs
            let rnOther = extendExprNameUses env o
            EMatch (rnCs, rnOther)
        | EIf (c, t, e) -> EIf (extendExprNameUses env c, extendStmtsNameUses env t, extendStmtsNameUses env e)
        | EWhile (c, b) -> EWhile (extendExprNameUses env c, extendStmtsNameUses env b)
        | EForEffect (assign, b) ->
            let assignEnv = addLocalNames env (List.map (fun (a: ForAssignClause) -> a.Name) assign)
            EForEffect (List.map (extendForAssignNameUses env) assign, extendStmtsNameUses assignEnv b)
        | EForComprehension (r, assign, b) ->
            let assignEnv = addLocalNames env (List.map (fun (a: ForAssignClause) -> a.Name) assign)
            EForComprehension (r, List.map (extendForAssignNameUses env) assign, extendStmtsNameUses assignEnv b)
        | EForFold (accs, assign, b) ->
            let accsEnv = addLocalNames env (List.map (fun (a: ForFoldInit) -> a.Name) accs)
            let assignEnv = addLocalNames accsEnv (List.map (fun (a: ForAssignClause) -> a.Name) assign)
            EForFold (
                List.map (extendForInitNameUses env) accs,
                List.map (extendForAssignNameUses env) assign,
                extendStmtsNameUses assignEnv b)
        | EFunctionLiteral b -> EFunctionLiteral (extendExprNameUses env b)
        | ETupleLiteral exp -> ETupleLiteral (extendExprNameUses env exp)
        | EListLiteral exp -> EListLiteral (extendExprNameUses env exp)
        | EVectorLiteral _ -> failwith "Renaming on vector literals not yet implemented."
        | ESliceLiteral _ -> failwith "Renaming on slice constructors not yet implemented."
        | ERecordLiteral exp -> ERecordLiteral (extendExprNameUses env exp)
        | EVariantLiteral (lbl, varVal) -> EVariantLiteral (lbl, extendExprNameUses env varVal)
        | ECase (cs, e) ->
            ECase (List.map (fun c -> { c with Body = extendExprNameUses env c.Body }) cs, extendExprNameUses env e)
        | EWithPermission (ps, thenSs, elseSs) ->
            EWithPermission (ps, extendStmtsNameUses env thenSs, extendStmtsNameUses env elseSs)
        | EIfPermission (ps, thenSs, elseSs) ->
            EIfPermission (ps, extendStmtsNameUses env thenSs, extendStmtsNameUses env elseSs)
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
            let letEnv = addLocalNames env (Boba.Core.DotSeq.toList ps |> List.collect patternNames)
            let rnPats = Boba.Core.DotSeq.map (extendPatternNameUses env) ps
            (letEnv, SLet { Matcher = rnPats; Body = List.map (extendWordNameUses env) vals })
        | SLocals _ -> failwith "Renaming of local functions is not yet implemented."
        | SExpression wds -> (env, SExpression (List.map (extendWordNameUses env) wds))
    and extendHandlerNameUses env handler =
        let bodyEnv = addLocalNames env handler.Params
        { handler with Name = dequalifyIdent env handler.Name; Body = extendExprNameUses bodyEnv handler.Body }
    and extendMatchClauseNameUses env clause =
        let matcher = Boba.Core.DotSeq.map (extendPatternNameUses env) clause.Matcher
        let patVars =  Boba.Core.DotSeq.toList clause.Matcher |> List.collect patternNames
        let bodyEnv = addLocalNames env patVars
        let body = extendExprNameUses bodyEnv clause.Body
        { Matcher = matcher; Body = body }
    and extendForAssignNameUses env clause =
        { clause with Assigned = extendExprNameUses env clause.Assigned }
    and extendForInitNameUses env clause =
        { clause with Assigned = extendExprNameUses env clause.Assigned }

    let rec extendKindNameUses env ki =
        match ki with
        | SKBase n -> SKBase (dequalifyIdent env n)
        | SKRow k -> SKRow (extendKindNameUses env k)
        | SKSeq k -> SKSeq (extendKindNameUses env k)
        | SKArrow (l, r) -> SKArrow (extendKindNameUses env l, extendKindNameUses env r)
        | SKWildcard -> SKWildcard

    let rec extendTypeNameUses env ty =
        match ty with
        | STCon ident -> STCon (dequalifyIdent env ident)
        | STAnd (l, r) -> STAnd (extendTypeNameUses env l, extendTypeNameUses env r)
        | STOr (l, r) -> STOr (extendTypeNameUses env l, extendTypeNameUses env r)
        | STNot b -> STNot (extendTypeNameUses env b)
        | STExponent (l, p) -> STExponent (extendTypeNameUses env l, p)
        | STMultiply (l, r) -> STMultiply (extendTypeNameUses env l, extendTypeNameUses env r)
        | STSeq (s, k) -> STSeq (Boba.Core.DotSeq.map (extendTypeNameUses env) s, k)
        | STApp (l, r) -> STApp (extendTypeNameUses env l, extendTypeNameUses env r)
        | _ -> ty
    
    let extendConstraintNameUses env ty =
        match ty with
        | SCPredicate ty -> SCPredicate (extendTypeNameUses env ty)
        | SCEquality (l, r) -> SCEquality (extendTypeNameUses env l, extendTypeNameUses env r)

    let extendFnNameUses env (fn : Function) =
        { fn with Body = List.map (extendWordNameUses env) fn.Body }
    
    let extendNativeNameUses env (nat : Native) =
        { nat with Type = extendTypeNameUses env nat.Type }

    let extendConstructorNameUses env ctorEnv (ctor : Constructor) =
        { ctor with
            Components = List.map (extendTypeNameUses env) ctor.Components
            Result = extendTypeNameUses ctorEnv ctor.Result }

    let extendDataTypeNameUses env ctorEnv (data : DataType) =
        let frame = List.map fst data.Params
        let newEnv = addLocalNames env frame
        let ctorEnv = addLocalNames ctorEnv frame
        { data with
            Params = List.map (fun (n, k) -> (n, extendKindNameUses ctorEnv k)) data.Params
            Constructors = List.map (extendConstructorNameUses newEnv ctorEnv) data.Constructors
            Kind = extendKindNameUses ctorEnv data.Kind }
    
    let extendUserKindNameUses env (kind : UserKind) = kind
    
    let extendDeclNameUses program prefix env decl =
        match decl with
        | DFunc fn ->
            let scope = Map.add fn.Name.Name prefix Map.empty
            scope, DFunc (extendFnNameUses env fn)
        | DRecFuncs fns ->
            let recScope = namesToPrefixFrame prefix (declNames decl)
            let rnFns = List.map (extendFnNameUses (addPrefixNames env recScope)) fns
            recScope, DRecFuncs (rnFns)
        | DNative fn ->
            let scope = Map.add fn.Name.Name prefix Map.empty
            scope, DNative (extendNativeNameUses env fn)
        | DTest t ->
            let scope = Map.add t.Name.Name prefix Map.empty
            scope, DTest { t with Left = extendExprNameUses env t.Left; Right = extendExprNameUses env t.Right }
        | DLaw l ->
            let scope = Map.add l.Name.Name prefix Map.empty
            let modParams = [for p in l.Params -> { p with Generator = extendExprNameUses env p.Generator }]
            let newEnv = addPrefixNames env (namesToFrame [for p in l.Params -> p.Name])
            scope, DLaw { l with Params = modParams; Left = extendExprNameUses newEnv l.Left; Right = extendExprNameUses newEnv l.Right }
        | DEffect e ->
            let hdlrNames = List.map (fun (h: HandlerTemplate) -> h.Name) e.Handlers
            let scope = Map.add e.Name.Name prefix (namesToPrefixFrame prefix hdlrNames)
            let extHandlers = List.map (fun (h: HandlerTemplate) -> { h with Type = extendTypeNameUses (addPrefixNames env scope) h.Type }) e.Handlers
            let extParams = [for p in e.Params -> (fst p, extendKindNameUses env (snd p))]
            scope, DEffect { e with Handlers = extHandlers; Params = extParams }
        | DCheck c ->
            Map.empty, DCheck { c with Matcher = extendTypeNameUses env c.Matcher }
        | DType d ->
            let recScope = namesToPrefixFrame prefix [d.Name]
            let scope = namesToPrefixFrame prefix (declNames decl)
            scope, DType (extendDataTypeNameUses env (addPrefixNames env recScope) d)
        | DKind k ->
            let scope = namesToPrefixFrame prefix (declNames decl)
            scope, DKind (extendUserKindNameUses env k)
        | DRecTypes ds ->
            let recScope = namesToPrefixFrame prefix (List.map (fun (d : DataType) -> d.Name) ds)
            let scope = namesToPrefixFrame prefix (declNames decl)
            scope, DRecTypes (List.map (extendDataTypeNameUses (addPrefixNames env recScope) (addPrefixNames env recScope)) ds)
        | DOverload o ->
            let scope = namesToPrefixFrame prefix [o.Name; o.Predicate]
            scope, DOverload { o with Template = extendTypeNameUses (addPrefixNames env scope) o.Template }
        | DInstance i ->
            let inst = {
                Name = dequalifyIdent env i.Name;
                Docs = i.Docs;
                Context = Boba.Core.DotSeq.map (extendTypeNameUses env) i.Context;
                Heads = List.map (extendTypeNameUses env) i.Heads;
                Body = extendExprNameUses env i.Body
            }
            Map.empty, DInstance inst
        | DPropagationRule r ->
            let expHd = List.map (extendTypeNameUses env) r.Head
            let expRes = List.map (extendConstraintNameUses env) r.Result
            Map.empty, DPropagationRule { r with Head = expHd; Result = expRes }
        | DClass c ->
            let frame = namesToFrame c.Params
            Map.empty, DClass { c with Expand = List.map (extendTypeNameUses (addPrefixNames env frame)) c.Expand }
        | DTag t ->
            let scope = namesToPrefixFrame prefix [t.TypeName; t.TermName]
            scope, DTag t
        | DPattern p ->
            let scope = namesToPrefixFrame prefix [p.Name]
            let paramScope = namesToPrefixFrame "" p.Params
            scope, DPattern { p with Expand = extendPatternNameUses (addPrefixNames env paramScope) p.Expand }
        | DTypeSynonym s ->
            let frame = namesToFrame s.Params
            let scope = namesToPrefixFrame prefix [s.Name]
            scope, DTypeSynonym { s with Expand = extendTypeNameUses (addPrefixNames env frame) s.Expand }
        | _ -> failwith $"Renaming not implemented for declaration '{decl}'"

    let rec extendDeclsNameUses program prefix env decls =
        match decls with
        | [] -> env, []
        | d :: ds ->
            let (scope, decl) = extendDeclNameUses program prefix env d
            let combined = { env with Names = mapUnion snd env.Names scope }
            let (finalScope, decls) = extendDeclsNameUses program prefix combined ds
            finalScope, decl :: decls

    let extendUnitNameUses loadedPrims program prefix unit =
        let env = importsScope program loadedPrims (unitImports unit)
        let env = { env with Examining = prefix }
        let (extendedEnv, rnDecls) = extendDeclsNameUses program prefix env (unitDecls unit)
        let extDecls = List.map (extendDeclName prefix) rnDecls
        match unit with
        | UMain (is, _, b) -> UMain (is, extDecls, extendExprNameUses extendedEnv b)
        | UExport (is, _, rexps, exp) -> UExport (is, extDecls, rexps, exp)

    let renameUnitDecls primEnv program (unit: PathUnit) =
        let prefix = pathToNamePrefix unit.Path
        extendUnitNameUses primEnv program prefix unit.Unit

    let isNative decl =
        match decl with
        | DNative _ -> true
        | _ -> false

    let isMain unit =
        match unit with
        | UMain _ -> true
        | UExport _ -> false

    /// Given an organized program (where the units are all in the proper dependency order, i.e. least dependent earlier
    /// in the list), extend all the names present in the program to be fully qualified, and erase the modules. The
    /// result is a list of declarations in lexical scoping order. We also return the list of fully qualified names
    /// in the start module, to make later compiler phases that only analyze the start module possible after renaming.
    let rename (program : OrganizedProgram) =
        let primEnv = { Aliases = Map.empty; Names = Map.empty; Examining = "main" }
        let renamedMain = renameUnitDecls primEnv program program.Main
        let units = List.append (List.map (renameUnitDecls primEnv program) program.Units) [renamedMain]
        let decls = List.collect unitDecls units
        let natives = [
            for i, u in List.mapi (fun i u -> (i, u)) units ->
            { UnitName = $"natUnit{i}";
              Imports = [for i in unitImports u do if i.Native then yield i.Path];
              Natives = [for d in unitDecls u do if isNative d then yield (declNames d).Head] }] 
        let mains = List.filter isMain units
        match mains with
        | [UMain (is, _, b)] ->
            let newUnit = { Natives = natives; Declarations = decls; Main = b }
            newUnit, [for d in unitDecls renamedMain do declNames d] |> List.concat
        | [] -> failwith "No main module found"
        | _ -> failwith "More than one main module found."
