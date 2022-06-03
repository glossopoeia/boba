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

    let unitTestToFunction (test : Test) =
        DFunc { Name = test.Name; Docs = []; Body = testExprToSimpleExpr test.Left test.Right test.Kind }

    let testToFunction testDecl =
        match testDecl with
        | DTest test -> unitTestToFunction test
        | DLaw law -> failwith "testToFunction not yet implemented for laws."
        | _ -> failwith "Somehow got a non-test in testToFunction."

    let testToCall test =
        match test with
        | DTest t -> EIdentifier { Qualifier = []; Name = t.Name; }
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
        EString { Value = $"\"{s}\""; Position = Position.Empty }

    let checkName = { Name = "test-check!"; Kind = IOperator; Position = Position.Empty; }
    let checkIdent = { Qualifier = []; Name = checkName; }

    let stTyVar name = STVar { Name = name; Kind = ISmall; Position = Position.Empty; }

    /// The type of test-check! is:
    /// {(--> (test-check! | e) p t [Bool^s1 (String v clear)^s2] []) false}
    /// TODO: need to add Boolean effect parameter that is and-accumulated throughout
    /// the computation so main knows whether to return 1 or 0 as the overall program output
    /// for a test run (1 if failure, 0 if success)
    let generateTestCheckType =
        let boolArgType = STApp (STApp (STPrim PrValue, STCon (Syntax.sIdentifier [] (Syntax.stringToBigName "Bool"))), stTyVar "s1")
        let stringArgType = STApp (STApp (STPrim PrValue, STApp (STApp (STPrim PrString, stTyVar "v2"), STTrue)), stTyVar "s2")
        let testCheckFnInput = STSeq (Boba.Core.DotSeq.ofList [stringArgType; boolArgType], KValue)
        let testCheckFnOutput = STSeq (Boba.Core.DotSeq.SEnd, KValue)
        let testEffRow = STApp (STApp (STRowExtend, STCon {Qualifier = []; Name = {Name = "test-check!"; Kind = IOperator; Position = Position.Empty} }), stTyVar "e")
        let testCheckFnType = STApp (STApp (STApp (STApp (STApp (STPrim PrFunction, testEffRow), stTyVar "p"), stTyVar "t"), testCheckFnInput), testCheckFnOutput)
        STApp (STApp (STPrim PrValue, testCheckFnType), STFalse)

    let generateTestEffect =
        DEffect {
            Name = checkName;
            Docs = [];
            Params = [];
            Handlers = [{
                Name = checkName;
                Type = STApp (STApp (STPrim PrQual, STApp (STPrim PrConstraintTuple, STSeq (Boba.Core.DotSeq.SEnd, KConstraint))), generateTestCheckType) }]
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
            Params = [testSuccessParam; testNameParam];
            Body = [
                EIf([genSmallEIdent "b"],
                    [SExpression[genSmallEIdent "i"; stringToStringLiteral " succeeded.\\n";]],
                    [SExpression[genSmallEIdent "i"; stringToStringLiteral " failed.\\n";]]);
                genSmallEIdent "string-concat";
                genSmallEIdent "print";
                genSmallEIdent "resume"]
        }

        // TODO: add handler parameter to thread an accumulated success Boolean through the test run,
        // and return 1 if this boolean is true (at least one failed), or 0 if the boolean is false (none failed)
        [EHandle ([],handled,[checkHandler],[]); EInteger { Value = "0"; Size = I32; Position = Position.Empty }]

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

    let emptyMain (program : OrganizedProgram) =
        { program with
            Main = {
                Path = program.Main.Path;
                Unit = UMain (unitImports program.Main.Unit, unitDecls program.Main.Unit, [EInteger { Value = "0"; Size = I32; Position = Position.Empty }])
            } }