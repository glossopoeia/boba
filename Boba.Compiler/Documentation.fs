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

    let fnType (name: string) =
        if name[name.Length-1] = '?'
        then "test"
        else "func"

    let generateFunction simplifier env (fn : Function) =
        match Environment.lookup env fn.Name.Name with
        | Some sch -> [
            Heading (3, [
                Literal ($"*{fnType fn.Name.Name}* " + fn.Name.Name + " : ", None)], None);
            Paragraph ([
                Literal("**Type**: ", None); 
                InlineCode (Types.prettyType (simplifier sch.Type.Body), None)], None);
            Paragraph (docsToMarkdown fn.Docs, None);
            HorizontalRule ('-', None)]
        | None -> failwith $"Could not find type for {fn.Name.Name} when generating documentation."
    
    let generateNative simplifier env (fn : Native) =
        match Environment.lookup env fn.Name.Name with
        | Some sch -> [
            Heading (3, [
                Literal ($"*native* " + fn.Name.Name + " : ", None)], None);
            Paragraph ([
                Literal("**Type**: ", None); 
                InlineCode (Types.prettyType (simplifier sch.Type.Body), None)], None);
            Paragraph (docsToMarkdown fn.Docs, None);
            HorizontalRule ('-', None)]
        | None -> failwith $"Could not find type for native function {fn.Name.Name} when generating documentation."
    
    let generateKind simplifier env (k : UserKind) =
        match Environment.lookupKind env k.Name.Name with
        | Some sch -> [
            Heading (3, [
                Literal ($"*kind* " + k.Name.Name + " : ", None);
                InlineCode ($"{k.Unify}", None)], None);
            Paragraph (docsToMarkdown k.Docs, None);
            HorizontalRule ('-', None)]
        | None -> failwith $"Could not find entry for kind {k.Name.Name} when generating documentation."
    
    let generatePattern simplifier env (p : PatternSynonym) =
        match Environment.lookupPattern env p.Name.Name with
        | Some sch -> [
            Heading (3, [
                Literal ($"*pattern* " + p.Name.Name + " : ", None)], None);
            Paragraph ([
                Literal("**Type**: ", None); 
                InlineCode (Types.prettyType (simplifier sch.Body), None)], None);
            Paragraph (docsToMarkdown p.Docs, None);
            HorizontalRule ('-', None)]
        | None -> failwith $"Could not find type for pattern {p.Name.Name} when generating documentation."
    
    let generateOverload simplifier env (o : Overload) =
        match Environment.lookup env o.Name.Name with
        | Some sch -> [
            Heading (3, [
                Literal ($"*overload* " + o.Name.Name + " : ", None)], None);
            Paragraph ([
                Literal("**Type**: ", None); 
                InlineCode (Types.prettyType (simplifier sch.Type.Body), None)], None);
            Paragraph (docsToMarkdown o.Docs, None);
            HorizontalRule ('-', None)]
        | None -> failwith $"Could not find type for pattern {o.Name.Name} when generating documentation."
    
    let generateDecl shouldOutput simplifier env decl =
        if List.exists (fun (n: Name) -> shouldOutput n.Name) (declNames decl)
        then
            match decl with
            | DFunc f -> generateFunction simplifier env f
            | DRecFuncs fs -> List.collect (generateFunction simplifier env) fs
            | DNative n -> generateNative simplifier env n
            | DKind k -> generateKind simplifier env k
            | _ ->
                printfn $"Warning: documentation for {declNames decl} unimplemented."
                []
        else []
    
    let generate unitName shouldOutput simplifier env decls =
        let ts = generateTitle unitName
        let ds = List.collect (generateDecl shouldOutput simplifier env) (List.rev decls)
        let doc = MarkdownDocument (List.append ts ds, new Dictionary<string, (string * string option)>())
        Markdown.ToMd doc
