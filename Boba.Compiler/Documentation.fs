namespace Boba.Compiler

module Documentation =

    open System.Collections.Generic
    open FSharp.Formatting.Markdown
    open FSharp.Formatting
    open Syntax
    open Boba.Core

    let docsToMarkdown docLines =
        let uncommented = [for d in docLines -> d.Line[3..]]
        let uncommented = String.concat "\n" uncommented
        match (Markdown.Parse uncommented).Paragraphs with
        | [] -> []
        | [Paragraph (body, _)] -> body
        | other -> failwith $"Unrecognized markdown documentation format {other}"

    let generateTitle title = [
        Heading (1, [Literal(title, None)], None)]
        
    let generateFunction simplifier env (fn : Function) =
        match Environment.lookup env fn.Name.Name with
        | Some sch -> [
            Heading (3, [
                Literal (fn.Name.Name + " : ", None);
                InlineCode (Types.prettyType (simplifier sch.Type.Body), None)], None);
                Paragraph (docsToMarkdown fn.Docs, None);
                HorizontalRule ('-', None)]
        | None -> failwith $"Could not find type for {fn.Name.Name} when generating documentation."
    
    let generateDecl shouldOutput simplifier env decl =
        if List.exists (fun (n: Name) -> shouldOutput n.Name) (declNames decl)
        then
            match decl with
            | DFunc f -> generateFunction simplifier env f
            | DRecFuncs fs -> List.collect (generateFunction simplifier env) fs
            | _ ->
                printfn $"Warning: documentation for {declNames decl} unimplemented."
                []
        else []
    
    let generate unitName shouldOutput simplifier env decls =
        let ts = generateTitle unitName
        let ds = List.collect (generateDecl shouldOutput simplifier env) (List.rev decls)
        let doc = MarkdownDocument (List.append ts ds, new Dictionary<string, (string * string option)>())
        Markdown.ToMd doc
