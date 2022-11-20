namespace Boba.Compiler

// Takes an organized program, and all the tests in the main module, and overwrites the main
// function definition with calls to those tests.
module TestGenerator =

    open Boba.Core
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

    let genSmallEIdent name = EIdentifier { Qualifier = []; Name = stringToSmallName name }

    let eqIdent = genSmallEIdent "eq"
    let boolNotIdent = genSmallEIdent "not-bool"
    let clearStringIdent = genSmallEIdent "clear-string"
    let gatherIdent = genSmallEIdent "gather"
    let spreadIdent = genSmallEIdent "spread"

    let letVar v body = 
        SLet {
            Matcher = DotSeq.ind (PNamed (stringToSmallName v, PWildcard)) DotSeq.SEnd;
            Body = body }

    let genMultiEq left right comparison = [
        EStatementBlock [
            letVar "$p" [gatherIdent];
            letVar "$l" (List.append left [gatherIdent]);
            letVar "$r" (List.append right [gatherIdent]);
            letVar "$c" (List.append [genSmallEIdent "$l"; genSmallEIdent "$r"] comparison);
            SExpression [genSmallEIdent "$p"; spreadIdent; genSmallEIdent "$c"]]]

    let testExprToSimpleExpr left right testKind =
        match testKind with
        | TKSatisfies -> List.append left right
        | TKViolates -> append3 left right [boolNotIdent]
        | TKIsRoughly -> failwith "is-roughly test generation is not yet implemented."
        | TKIs [] -> genMultiEq left right [eqIdent]
        | TKIsNot [] -> genMultiEq left right [eqIdent; boolNotIdent]
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
        let callTest t = [
            testToCall t;
            stringToStringLiteral (testName t);
            clearStringIdent;
            EIdentifier checkIdent]

        let handled =
            List.collect callTest tests
            |> List.append [intToIntegerLiteral 0]
            |> SExpression
            |> List.singleton

        let addPatVar s v = DotSeq.ind (PNamed (stringToSmallName v, PWildcard)) s

        let checkHandler : Boba.Compiler.Syntax.Handler = {
            Name = checkIdent;
            Body = [
                EStatementBlock [
                    SLet {
                        Matcher = List.fold addPatVar DotSeq.SEnd ["f"; "b"; "i"];
                        Body = [] };
                    SExpression [
                        genSmallEIdent "b";
                        genSmallEIdent "i";
                        genSmallEIdent "f"
                        genSmallEIdent "test-check-handler";
                        genSmallEIdent "resume"]]
                ]
        }

        [EHandle (1, [],handled,[checkHandler],([]))]

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
                Unit = UMain (
                    unitImports program.Main.Unit,
                    List.map testToFunction (unitDecls program.Main.Unit),
                    [intToIntegerLiteral 0])
            } }