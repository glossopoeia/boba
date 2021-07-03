namespace Boba.Compiler

/// Renaming takes aliased and imported names present in the definitions of all declarations of a unit,
/// and turns them into their fully-qualified counter parts. This allows the renaming phase to erase
/// module import and export statements, leaving only the list of top-level declarations.
module Renamer =

    open Boba.Core.Common
    open Syntax
    open UnitDependencies

    type RenamedProgram = { Declarations: List<Declaration>; Main: List<Word> }



    //let rename (prg : OrganizedProgram) =
    //    let moduleNames = Map.map (constant unitDeclNames) prg.Units
    //    moduleNames
