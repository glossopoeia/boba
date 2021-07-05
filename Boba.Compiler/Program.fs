namespace Boba.Compiler


module Main =

    open System
    open System.IO
    open FSharp.Text.Lexing
    open Bubl.Simulator

    [<EntryPoint>]
    let main argv =
        
        Console.WriteLine("Enter the name of a file to compile...");

        let filename = Console.ReadLine()

        let lexbuf = LexBuffer<char>.FromString (File.ReadAllText filename)
        
        let ast = Parser.unit Lexer.token lexbuf
        Console.WriteLine(ast)

        let program: Syntax.Program = { Units = Map.empty; Main = ast }

        let organized = UnitDependencies.organize program
        let renamed = Renamer.rename organized
        let condensed = Condenser.genCondensed renamed
        let core = CoreGen.genCoreProgram condensed
        let bubl = BublGen.genProgram core

        let initial = Machine.newMachine bubl
        let result = Evaluation.run initial

        Console.WriteLine(result.Stack)
        0