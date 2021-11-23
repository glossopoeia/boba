namespace Boba.Compiler


module Main =

    open System
    open System.IO
    open FSharp.Text.Lexing
    open Mochi.Simulator

    let rec copyDirRec src dest =
        if not <| System.IO.Directory.Exists(dest) then
            System.IO.Directory.CreateDirectory(dest) |> ignore

        let srcDir = DirectoryInfo(src)

        for file in srcDir.GetFiles() do
            let temppath = System.IO.Path.Combine(dest, file.Name)
            file.CopyTo(temppath, true) |> ignore

        for subdir in srcDir.GetDirectories() do
            let dstSubDir = System.IO.Path.Combine(dest, subdir.Name)
            copyDirRec subdir.FullName dstSubDir

    [<EntryPoint>]
    let main argv =

        if argv.Length < 2
        then
            Console.WriteLine("Boba compiler expects 2 arguments!")

        let lexbuf = LexBuffer<char>.FromString (File.ReadAllText argv.[1])
        
        let ast = 
            try
                Parser.unit Lexer.token lexbuf
            with e ->
                Console.WriteLine($"Parse failed at: {lexbuf.EndPos.Line}, {lexbuf.EndPos.Column}")
                Console.WriteLine($"    with '{String(lexbuf.Lexeme)}'")
                exit 1
        Console.WriteLine(ast)

        if argv.[0] <> "test"
        then
            let program: Syntax.Program = { Units = Map.empty; Main = ast }

            let organized = UnitDependencies.organize program
            let renamed = Renamer.rename organized
            let condensed = Condenser.genCondensed renamed
            let core = CoreGen.genCoreProgram condensed
            let mochi = MochiGen.genProgram core

            copyDirRec "./mochivm" "./output"

            let sw = new StreamWriter("./output/main.c")
            BytecodeGen.writeBlocks sw mochi
            sw.Flush()

            //let initial = Machine.newMachine mochi
            //let result = Evaluation.run initial

            //Console.WriteLine(result.Stack)
            Console.WriteLine("build successful")
            0
        else
            Console.WriteLine("testing is not yet implemented!")
            0