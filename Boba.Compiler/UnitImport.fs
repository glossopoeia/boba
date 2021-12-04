namespace Boba.Compiler

module UnitImport =

    open System
    open System.IO
    open System.Net.Http
    open FSharp.Text.Lexing
    open Syntax

    let parseModule modulePath buffer =
        try
            Parser.unit Lexer.token buffer
        with e ->
            failwith $"Parse failed in '{modulePath}' at: {buffer.EndPos.Line}, {buffer.EndPos.Column}\n    with '{String(buffer.Lexeme)}'"

    let getModuleText modulePath =
        match modulePath with
        | IPLocal local ->
            let fileName = local.Value.Substring(1, (local.Value.Length - 2))
            File.ReadAllText $"{fileName}.boba"
        | IPRemote name ->
            let url = $"https://github.com/{name.Org}/{name.Project}/{name.Unit}.boba"
            (new HttpClient()).GetStringAsync(url) |> Async.AwaitTask |> Async.RunSynchronously

    let loadModule path =
        getModuleText path
        |> LexBuffer<char>.FromString
        |> parseModule path

    let rec loadDependencies alreadySeen imports loaded =
        match imports with
        | [] -> loaded
        | i :: is ->
            if not (List.contains i alreadySeen)
            then
                let load = loadModule i
                let newImps = unitImports load |> List.map (fun imp -> imp.Path)
                loadDependencies (i :: alreadySeen) (List.append is newImps) (Map.add i load loaded)
            else loadDependencies alreadySeen is loaded

    let loadProgram entryPath =
        let start = loadModule entryPath
        let imports = unitImports start |> List.map (fun imp -> imp.Path)
        let deps = loadDependencies [entryPath] imports Map.empty
        { Units = deps; Main = start }