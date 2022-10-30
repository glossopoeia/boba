namespace Boba.Compiler

module Condenser =
    
    open Boba.Core.Types
    open Boba.Core.TypeBuilder
    open Boba.Core
    open Boba.Compiler.Syntax
    open Boba.Compiler.Renamer



    type Handler = {
        Name: string;
        Inputs: int;
        Outputs: int;
    }
    
    type Effect = {
        Name: string;
        Handlers: List<Handler>;
    }

    type Native = {
        UnitName: string;
        Imports: List<ImportPath>;
        Decls: List<Syntax.Native>
    }

    type CondensedProgram = {
        Main: List<Word>;
        Definitions: List<(string * List<Word>)>;
        Constructors: List<Constructor>;
        Effects: List<Effect>;
        Natives: List<Native>;
    }

    let getCtors decls =
        [
            for d in decls do
                match d with
                | DType dt -> yield dt.Constructors
                | DRecTypes dts -> yield [for dt in dts -> dt.Constructors] |> List.concat
                | _ -> yield []
        ]
        |> List.concat

    let rec substPattern subst pat =
        match pat with
        | PTuple ps -> PTuple (DotSeq.map (substPattern subst) ps)
        | PList ps -> PList (DotSeq.map (substPattern subst) ps)
        | PVector _ -> failwith "Vector patterns not yet implemented."
        | PSlice _ -> failwith "Slice patterns not yet implemented."
        | PRecord fs -> PRecord (List.map (fun f -> fst f, substPattern subst (snd f)) fs)
        | PConstructor (n, args) -> PConstructor (n, DotSeq.map (substPattern subst) args)
        | PRef p -> PRef (substPattern subst p)
        | PNamed (n, PWildcard) ->
            if Map.containsKey n.Name subst
            then subst.[n.Name]
            else pat
        | _ -> pat
    
    let rec expandPattern subst pat =
        match pat with
        | PTuple ps -> PTuple (DotSeq.map (expandPattern subst) ps)
        | PList ps -> PList (DotSeq.map (expandPattern subst) ps)
        | PVector _ -> failwith "Vector patterns not yet implemented."
        | PSlice _ -> failwith "Slice patterns not yet implemented."
        | PRecord fs -> PRecord (List.map (fun f -> fst f, expandPattern subst (snd f)) fs)
        | PConstructor (n, args) ->
            if Map.containsKey n.Name.Name subst
            then
                let subArgs = DotSeq.map (expandPattern subst) args
                let pars, exp = subst.[n.Name.Name]
                let gen = substPattern (Map.ofSeq (List.zip (List.rev pars) (DotSeq.toList subArgs))) exp
                gen
            else pat
        | PRef p -> PRef (expandPattern subst p)
        | PNamed (n, p) -> PNamed (n, expandPattern subst p)
        | _ -> pat
    
    let rec expandPatternSynonyms subst expr = [for w in expr -> expandPatternSynonymsWord subst w]
    and expandPatternSynonymsWord subst word =
        match word with
        | EStatementBlock ss -> EStatementBlock (expandPatternSynonymsStatements subst ss)
        | ENursery (n, ss) -> ENursery (n, expandPatternSynonymsStatements subst ss)
        | ECancellable (n, ss) -> ECancellable (n, expandPatternSynonymsStatements subst ss)
        | EHandle (rc, ps, hdld, hdlrs, aft) ->
            EHandle (rc, ps,
                expandPatternSynonymsStatements subst hdld,
                List.map (expandPatternSynonymsHandler subst) hdlrs,
                expandPatternSynonyms subst aft)
        | EInject (effs, ss) -> EInject (effs, expandPatternSynonymsStatements subst ss)
        | EMatch (cs, o) -> EMatch (List.map (expandPatternSynonymsMatchClause subst) cs, expandPatternSynonyms subst o)
        | EIf (c, t, e) -> EIf (expandPatternSynonyms subst c, expandPatternSynonymsStatements subst t, expandPatternSynonymsStatements subst e)
        | EWhile (c, b) -> EWhile (expandPatternSynonyms subst c, expandPatternSynonymsStatements subst b)
        | EFunctionLiteral b -> EFunctionLiteral (expandPatternSynonyms subst b)
        | ETupleLiteral b -> ETupleLiteral (expandPatternSynonyms subst b)
        | EListLiteral b -> EListLiteral (expandPatternSynonyms subst b)
        | EVectorLiteral _ -> failwith "Vector literals not yet implemented."
        | ESliceLiteral _ -> failwith "Slice literals not yet implemented."
        | ERecordLiteral exp -> ERecordLiteral (expandPatternSynonyms subst exp)
        | EVariantLiteral (n, v) -> EVariantLiteral (n, expandPatternSynonyms subst v)
        | ECase (cs, o) -> ECase (List.map (expandPatternSynonymsCase subst) cs, expandPatternSynonyms subst o)
        | EWithPermission (ps, thenSs, elseSs) ->
            EWithPermission (ps, expandPatternSynonymsStatements subst thenSs, expandPatternSynonymsStatements subst elseSs)
        | EIfPermission (ps, thenSs, elseSs) ->
            EIfPermission (ps, expandPatternSynonymsStatements subst thenSs, expandPatternSynonymsStatements subst elseSs)
        | EWithState ss -> EWithState (expandPatternSynonymsStatements subst ss)
        | _ -> word
    and expandPatternSynonymsStatements subst stmts = List.map (expandPatternSynonymsStatement subst) stmts
    and expandPatternSynonymsStatement subst stmt =
        match stmt with
        | SLet m -> SLet (expandPatternSynonymsMatchClause subst m)
        | SLocals _ -> failwith "Substitution for local functions not yet implemented."
        | SExpression e -> SExpression (expandPatternSynonyms subst e)
    and expandPatternSynonymsHandler subst hdlr =
        { hdlr with Body = expandPatternSynonyms subst hdlr.Body }
    and expandPatternSynonymsMatchClause subst clause =
        { clause with Matcher = DotSeq.map (expandPattern subst) clause.Matcher; Body = expandPatternSynonyms subst clause.Body }
    and expandPatternSynonymsCase subst case = { case with Body = expandPatternSynonyms subst case.Body }

    let getPatternSyns decls =
        [
            for d in decls ->
                match d with
                | DPattern p -> [p.Name.Name, ([for p in p.Params -> p.Name], p.Expand)]
                | _ -> []
        ]
        |> List.concat

    let getDefs decls =
        [
            for d in decls do
                match d with
                | DFunc f -> yield [(f.Name.Name, f.Body)]
                | DRecFuncs fs -> yield [for f in fs -> (f.Name.Name, f.Body)]
                | DTag t -> yield [(t.TermName.Name, [])]
                | DOverload o -> yield o.Bodies
                | _ -> yield []
        ]
        |> List.concat

    let getEffs decls env =
        [
            for d in decls do
                match d with
                | DEffect e ->
                    yield [{
                        Name = e.Name.Name;
                        Handlers = [
                            for h in e.Handlers ->
                                let (Some entry) = Environment.lookup env h.Name.Name
                                let _, _, _, (TSeq (ins, _)), (TSeq (outs, _)) = functionValueTypeComponents (qualTypeHead entry.Type.Body)
                                {
                                    Name = h.Name.Name;
                                    Inputs = removeSeqPoly ins |> DotSeq.length;
                                    Outputs = removeSeqPoly outs |> DotSeq.length;
                                }]
                }]
                | _ -> yield []
        ]
        |> List.concat

    let getNative decls (natName: Name) =
        [for d in decls do
            match d with
            | DNative n ->
                if n.Name.Name = natName.Name
                then yield [n]
                else yield []
            | _ -> yield []] |> List.concat
    
    let getNatives decls (nats: List<NativeSubset>) =
        [
            for n in nats do
                yield {
                    UnitName = n.UnitName;
                    Imports = n.Imports;
                    Decls = List.collect (getNative decls) n.Natives }
        ]

    let genCondensed (program : RenamedProgram) env =
        let ctors = getCtors program.Declarations
        let patSyns = Map.ofList (getPatternSyns program.Declarations)
        let defs = getDefs program.Declarations
        let patReplDefs = [for d in defs -> (fst d, expandPatternSynonyms patSyns (snd d))]
        let matchEffs = [
            for inp in 0..15 -> {
                Name = $"match{inp}!";
                Handlers =
                    { Name = $"$default{inp}!"; Inputs = inp; Outputs = 0 }
                    :: [for i in 0..99 -> { Name = $"$match{i}-{inp}!"; Inputs = inp; Outputs = 0 }]
            }
        ]
        let effs = List.append matchEffs (getEffs program.Declarations env)
        let nats = getNatives program.Declarations program.Natives
        { Main = expandPatternSynonyms patSyns program.Main;
          Definitions = patReplDefs;
          Constructors = ctors;
          Effects = effs;
          Natives = nats }