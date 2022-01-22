namespace Boba.Compiler

module Condenser =
    
    open Boba.Core.Types
    open Boba.Compiler.Syntax
    open Boba.Compiler.Renamer



    type Effect = {
        Name: string;
        Handlers: List<string>;
    }

    type CondensedProgram = {
        Main: List<Word>;
        Definitions: List<(string * List<Word>)>;
        Constructors: List<Constructor>;
        Effects: List<Effect>;
    }

    let getCtors decls =
        [
            for d in decls do
                match d with
                | DType dt -> yield dt.Constructors
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

    let genCondensed (program : RenamedProgram) =
        let ctors = getCtors program.Declarations
        let defs = getDefs program.Declarations
        let effs = getEffs program.Declarations
        { Main = program.Main; Definitions = defs; Constructors = ctors; Effects = effs; }