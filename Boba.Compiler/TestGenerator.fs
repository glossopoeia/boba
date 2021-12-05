namespace Boba.Compiler

// Takes an organized program, and all the tests in the main module, and overwrites the main
// function definition with calls to those tests.
module TestGenerator =

    open Boba.Core.Common
    open Boba.Core.Types
    open FSharp.Text.Lexing
    open Syntax
    open UnitDependencies

    let isTest decl =
        match decl with
        | DTest _ -> true
        | DLaw _ -> true
        | _ -> false

    let genSmallEIdent name = EIdentifier { Qualifier = []; Name = { Name = name; Kind = ISmall; Position = Position.Empty }; Size = None; }

    let eqIdent = genSmallEIdent "eq"
    let boolNotIdent = genSmallEIdent "bool-not"

    let testExprToSimpleExpr left right testKind =
        match testKind with
        | TKSatisfies -> List.append left right
        | TKViolates -> append3 left right [boolNotIdent]
        | TKIsRoughly -> failwith "is-roughly test generation is not yet implemented."
        | TKIs [] -> append3 left right [eqIdent]
        | TKIsNot [] -> append3 left right [eqIdent; boolNotIdent]
        | TKIs expr -> append3 left right expr
        | TKIsNot expr -> append3 left right (List.append expr [boolNotIdent])

    let unitTestToFunction (test : Test) =
        DFunc { Name = test.Name; FixedParams = []; Body = testExprToSimpleExpr test.Left test.Right test.Kind }

    let testToFunction testDecl =
        match testDecl with
        | DTest test -> unitTestToFunction test
        | DLaw law -> failwith "testToFunction not yet implemented for laws."
        | _ -> failwith "Somehow got a non-test in testToFunction."

    let testToCall test =
        match test with
        | DTest t -> EIdentifier { Qualifier = []; Name = t.Name; Size = None; }
        | DLaw t -> failwith "testToCall is not yet supported for laws."
        | _ -> failwith "Somehow got a non-test in testToCall."
    
    let testName test =
        match test with
        | DTest t -> t.Name.Name
        | DLaw l -> l.Name.Name
        | _ -> ""

    let intToIntegerLiteral (i: int) =
        EInteger { Value = i.ToString(); Size = I32; Position = Position.Empty; }

    let stringToStringLiteral (s: string) =
        EString { Value = s; Position = Position.Empty }

    let checkName = { Name = "test-check!"; Kind = IOperator; Position = Position.Empty; };
    let checkIdent = { Qualifier = []; Name = checkName; Size = None; }

    let generateTestEffect =
        DEffect {
            Name = checkName
            Params = [];
            Handlers = [{
                Name = checkName;
                FixedParams = [{ Name = "i"; Kind = ISmall; Position = Position.Empty }];
                Type = { Context = []; Head = TFixedConst 1 } }]
        }

    let generateTestMain tests =
        let handled =
            List.collect (fun t -> [testToCall t; stringToStringLiteral (testName t); EIdentifier checkIdent]) tests
            |> SExpression
            |> List.singleton

        let testSuccessParam = { Name = "b"; Kind = ISmall; Position = Position.Empty; }
        let testNameParam = { Name = "i"; Kind = ISmall; Position = Position.Empty; }
        let checkHandler = {
            Name = checkIdent;
            FixedParams = [];
            Params = [testSuccessParam; testNameParam];
            Body = [
                EIf([genSmallEIdent "b"],
                    [SExpression[genSmallEIdent "i"; stringToStringLiteral " succeeded.\\n";]],
                    [SExpression[genSmallEIdent "i"; stringToStringLiteral " failed.\\n";]]);
                genSmallEIdent "string-concat";
                genSmallEIdent "print";
                genSmallEIdent "resume"]
        }

        [EHandle ([],handled,[checkHandler],[])]

    let generateTestRunner (program : OrganizedProgram) =
        let decls = unitDecls program.Main.Unit
        let tests = List.filter isTest decls
        let transformed = List.map testToFunction tests
        let newDecls = append3 (List.filter (isTest >> not) decls) transformed [generateTestEffect]
        let newMain = generateTestMain tests
        { program with
            Main = {
                Path = program.Main.Path;
                Unit = UMain (unitImports program.Main.Unit, newDecls, newMain) } }
    
    let verifyHasMain (program : OrganizedProgram) =
        match program.Main.Unit with
        | UMain _ -> program
        | _ -> failwith "Cannot run a module with no main function. Maybe specify the 'test' flag, or compile with a different entry point unit."