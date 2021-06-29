namespace Boba.Compiler

module Condenser =
    
    open Boba.Core.Types
    open Boba.Compiler.Syntax



    type CondensedProgram = {
        Main: List<Word>;
        Definitions: List<(string * List<Word>)>;
        Constructors: List<(string * List<Type>)>;
    }



