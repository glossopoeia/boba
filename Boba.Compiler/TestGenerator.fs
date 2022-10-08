namespace Boba.Compiler

// Takes an organized program, and all the tests in the main module, and overwrites the main
// function definition with calls to those tests.
module TestGenerator =

    open Boba.Core.Common
    open Boba.Core.Types
    open Boba.Core.Kinds
    open FSharp.Text.Lexing
    open Syntax
    open UnitDependencies

    let isTest decl =
        match decl with
        | DTest _ -> true
        | DLaw _ -> true
        | _ -> false

    let genSmallEIdent name = EIdentifier { Qualifier = []; Name = { Name = name; Kind = ISmall; Position = Position.Empty } }

    let eqIdent = genSmallEIdent "eq"
    let boolNotIdent = genSmallEIdent "not-bool"

    let testExprToSimpleExpr left right testKind =
        match testKind with
        | TKSatisfies -> List.append left right
        | TKViolates -> append3 left right [boolNotIdent]
        | TKIsRoughly -> failwith "is-roughly test generation is not yet implemented."
        | TKIs [] -> append3 left right [eqIdent]
        | TKIsNot [] -> append3 left right [eqIdent; boolNotIdent]
        | TKIs expr -> append3 left right expr
        | TKIsNot expr -> append3 left right (List.append expr [boolNotIdent])
    
    let lawGeneratorsExprToSimpleExpr generators left right testKind =
        let lawAcc = stringToSmallName "law$Res"
        let body = testExprToSimpleExpr left right testKind
        let assigns = [for (g: LawParam) in generators -> { Name = g.Name; SeqType = FForIterator; Assigned = g.Generator }]
        let res = [{ Name = lawAcc; Assigned = [ETrue] }]
        [EForFold (res, assigns, [SExpression (List.concat [[genSmallEIdent "law$Res"]; body; [genSmallEIdent "and-bool"]])])]

    let unitTestToFunction (test : Test) =
        DFunc { Name = test.Name; Docs = []; Body = testExprToSimpleExpr test.Left test.Right test.Kind }
    
    let lawTestToFunction (law: Law) =
        DFunc { Name = law.Name; Docs = []; Body = lawGeneratorsExprToSimpleExpr law.Params law.Left law.Right law.Kind }

    let testToFunction testDecl =
        match testDecl with
        | DTest test -> unitTestToFunction test
        | DLaw law -> lawTestToFunction law
        | _ -> testDecl

    let testToCall test =
        match test with
        | DTest t -> EIdentifier { Qualifier = []; Name = t.Name; }
        | DLaw t -> EIdentifier { Qualifier = []; Name = t.Name; }
        | _ -> failwith "Somehow got a non-test in testToCall."
    
    let testName test =
        match test with
        | DTest t -> t.Name.Name
        | DLaw l -> l.Name.Name
        | _ -> ""

    let intToIntegerLiteral (i: int) =
        EInteger { Value = i.ToString(); Size = INative; Position = Position.Empty; }

    let stringToStringLiteral (s: string) =
        EString { Value = $"\"{s}\""; Position = Position.Empty }

    let checkName = { Name = "test-check!"; Kind = IOperator; Position = Position.Empty; }
    let checkIdent = { Qualifier = []; Name = checkName; }

    let generateTestMain tests =
        let handled =
            List.collect (fun t -> [testToCall t; stringToStringLiteral (testName t); EIdentifier checkIdent]) tests
            |> List.append [intToIntegerLiteral 0]
            |> SExpression
            |> List.singleton

        let testFailedParam = stringToSmallName "f"
        let testSuccessParam = stringToSmallName "b"
        let testNameParam = stringToSmallName "i"
        let checkHandler = {
            Name = checkIdent;
            Params = [testFailedParam; testSuccessParam; testNameParam];
            Body = [
                genSmallEIdent "b";
                genSmallEIdent "i";
                genSmallEIdent "f"
                genSmallEIdent "test-check-handler";
                genSmallEIdent "resume"]
        }

        [EHandle ([],handled,[checkHandler],[])]

    let generateTestRunner (program : OrganizedProgram) =
        let decls = unitDecls program.Main.Unit
        let tests = List.filter isTest decls
        let transformed = List.map testToFunction tests
        let newDecls = List.append (List.filter (isTest >> not) decls) transformed
        let newMain = generateTestMain tests
        { program with
            Main = {
                Path = program.Main.Path;
                ExportableNames = [];
                Unit = UMain (unitImports program.Main.Unit, newDecls, newMain) } }
    
    let verifyHasMain (program : OrganizedProgram) =
        match program.Main.Unit with
        | UMain (is, ds, m) -> { program with Main = { Path = program.Main.Path; ExportableNames = []; Unit = UMain (is, List.map testToFunction ds, m) } }
        | _ -> failwith "Cannot run a module with no main function. Maybe specify the 'test' flag, or compile with a different entry point unit."

    let emptyMain (program : OrganizedProgram) =
        { program with
            Main = {
                Path = program.Main.Path;
                ExportableNames = [];
                Unit = UMain (unitImports program.Main.Unit, List.map testToFunction (unitDecls program.Main.Unit), [EInteger { Value = "0"; Size = INative; Position = Position.Empty }])
            } }