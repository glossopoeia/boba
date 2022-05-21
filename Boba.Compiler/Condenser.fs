namespace Boba.Compiler

module Condenser =
    
    open Boba.Core.Types
    open Boba.Compiler.Syntax
    open Boba.Compiler.Renamer



    type Effect = {
        Name: string;
        Handlers: List<string>;
    }

    type Overload = {
        Name: string;
        Template: SType;
        Instances: List<(string * List<Word>)>
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

    let getDefs decls =
        [
            for d in decls do
                match d with
                | DFunc f -> yield [(f.Name.Name, f.Body)]
                | DRecFuncs fs -> yield [for f in fs -> (f.Name.Name, f.Body)]
                | DTag (_, t) -> yield [(t.Name, [])]
                | DOverload (n, p, t, bs) -> yield bs
                | _ -> yield []
        ]
        |> List.concat

    let getEffs decls =
        [
            for d in decls do
                match d with
                | DEffect e -> yield [{ Name = e.Name.Name; Handlers = [for h in e.Handlers -> h.Name.Name] }]
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

    let genCondensed (program : RenamedProgram) =
        let ctors = getCtors program.Declarations
        let defs = getDefs program.Declarations
        let matchEff = { Name = "match!"; Handlers = "$default!" :: [for i in 0..99 -> $"$match{i}!"] }
        let effs = matchEff :: getEffs program.Declarations
        let nats = getNatives program.Declarations program.Natives
        { Main = program.Main;
          Definitions = defs;
          Constructors = ctors;
          Effects = effs;
          Natives = nats }