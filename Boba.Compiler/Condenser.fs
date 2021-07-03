namespace Boba.Compiler

module Condenser =
    
    open Boba.Core.Types
    open Boba.Compiler.Syntax
    open Boba.Compiler.Renamer



    type CondensedProgram = {
        Main: List<Word>;
        Definitions: List<(string * List<Word>)>;
        Constructors: List<Constructor>;
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
        ]
        |> List.concat
        

    let genCondensed (program : RenamedProgram) =
        let ctors = getCtors program.Declarations
        let defs = getDefs program.Declarations
        { Main = program.Main; Definitions = defs; Constructors = ctors }