namespace Boba.Compiler

/// Renaming takes aliased and imported names present in the definitions of all declarations of a unit,
/// and turns them into their fully-qualified counter parts. This could allow the renaming phase to erase
/// module import and export statements, leaving only the list of top-level declarations, and indeed it
/// is one of the goals of renaming to allow this. 

/// TODO: is the below true?
/// However, renaming maintains this information for the dependency
/// organization phase which occurs immediately after this.
module Renamer =

    open Boba.Core.Common
    open Syntax

    type RenamedProgram = { Declarations: Map<string, Declaration>; Main: List<Word> }



    let rename (prg : Program) =
        let moduleNames = Map.map (constant unitDeclNames) prg.Modules
        moduleNames
