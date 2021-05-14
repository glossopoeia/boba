namespace Boba.Compiler

module Renamer =

    open Boba.Core.Common
    open Syntax

    type RenamedProgram = { Declarations: Map<string, Declaration>; Main: List<Word> }



    let rename (prg : Program) =
        let moduleNames = Map.map (constant unitDeclNames) prg.Modules
        moduleNames
