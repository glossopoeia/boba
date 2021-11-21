namespace Boba.Compiler


module Main =

    open System
    open System.IO
    open FSharp.Text.Lexing
    open Mochi.Simulator

    [<EntryPoint>]
    let main argv =
        
        Console.WriteLine("Enter the name of a file to compile...");

        let filename = Console.ReadLine()

        let lexbuf = LexBuffer<char>.FromString (File.ReadAllText filename)
        
        let ast = 
            try
                Parser.unit Lexer.token lexbuf
            with e ->
                Console.WriteLine($"Parse failed at: {lexbuf.EndPos.Line}, {lexbuf.EndPos.Column}")
                Console.WriteLine($"    with '{String(lexbuf.Lexeme)}'")
                exit 1
        Console.WriteLine(ast)

        let program: Syntax.Program = { Units = Map.empty; Main = ast }

        let organized = UnitDependencies.organize program
        let renamed = Renamer.rename organized
        let condensed = Condenser.genCondensed renamed
        let core = CoreGen.genCoreProgram condensed
        let Mochi = MochiGen.genProgram core

        let initial = Machine.newMachine Mochi
        let result = Evaluation.run initial

        Console.WriteLine(result.Stack)
        0