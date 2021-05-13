namespace Boba.Compiler


module Main =

    open System
    open System.IO
    open FSharp.Text.Lexing

    [<EntryPoint>]
    let main argv =
        
        Console.WriteLine("Enter the name of a file to compile...");

        let filename = Console.ReadLine()

        let lexbuf = LexBuffer<char>.FromString (File.ReadAllText filename)
        
        let ast = Parser.unit Lexer.token lexbuf
        Console.WriteLine(ast)

        0