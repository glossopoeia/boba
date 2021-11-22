namespace Boba.Compiler


module Main =

    open System
    open System.IO
    open FSharp.Text.Lexing
    open Mochi.Simulator

    [<EntryPoint>]
    let main argv =

        Console.WriteLine("Is this a compilation or a test?")
        let compileOrTest = Console.ReadLine()

        Console.WriteLine("Enter the name of a file to compile...")
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

        if compileOrTest <> "test"
        then
            let program: Syntax.Program = { Units = Map.empty; Main = ast }

            let organized = UnitDependencies.organize program
            let renamed = Renamer.rename organized
            let condensed = Condenser.genCondensed renamed
            let core = CoreGen.genCoreProgram condensed
            let mochi = MochiGen.genProgram core
            let sw = new StreamWriter("./mochivm/main.c")
            BytecodeGen.writeBlocks sw mochi
            sw.Flush()

            let initial = Machine.newMachine mochi
            let result = Evaluation.run initial

            Console.WriteLine(result.Stack)
            0
        else
            Console.WriteLine("testing is not yet implemented!")
            0