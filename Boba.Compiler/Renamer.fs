namespace Boba.Compiler

/// Renaming takes aliased and imported names present in the definitions of all declarations of a unit,
/// and turns them into their fully-qualified counter parts. This allows the renaming phase to erase
/// module import and export statements, leaving only the list of top-level declarations.
module Renamer =

    open Boba.Core.Common
    open Syntax
    open UnitDependencies

    type RenamedProgram = { Declarations: List<Declaration>; Main: List<Word> }

    let rename (program : OrganizedProgram) =
        //TODO: this current form does not actually do any renaming
        //TODO: this current form treats every definition as a global
        //TODO: this current form does not handle import aliases
        let decls = [for u in program.Units -> unitDecls u.Unit] |> List.concat
        let main =
            match program.Main with
            | UMain (_, _, b) -> b
        { Declarations = List.append decls (unitDecls program.Main); Main = main }
