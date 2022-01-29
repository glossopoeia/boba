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
        Instances: List<(SType * List<Word>)>
    }

    type CondensedProgram = {
        Main: List<Word>;
        Definitions: List<(string * List<Word>)>;
        Constructors: List<Constructor>;
        Overloads: List<Overload>;
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

    let getInstances (inst : Name) decls =
        [
            for d in decls do
                match d with
                | DInstance (n, t, b) when n.Name = inst.Name -> yield [(t, b)]
                | _ -> yield []
        ]
        |> List.concat

    let getOverloads decls =
        [
            for d in decls do
                match d with
                | DOverload (n, _, t) -> yield [{ Name = n.Name; Template = t; Instances = getInstances n decls }]
                | _ -> yield []
        ]
        |> List.concat

    let genCondensed (program : RenamedProgram) =
        let ctors = getCtors program.Declarations
        let defs = getDefs program.Declarations
        let effs = getEffs program.Declarations
        let overs = getOverloads program.Declarations
        { Main = program.Main; Definitions = defs; Constructors = ctors; Overloads = overs; Effects = effs; }