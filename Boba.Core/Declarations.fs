namespace Boba.Core

module Declarations =

    open Expression
    open Types

    type TestType =
        | TTIsRoughly
        | TTSatisfies
        | TTViolates
        | TTIs of Expression
        | TTIsNot of Expression

    type AdHocInstance = {
        Overloaded: QualifiedType;
        Body: Expression;
    }

    type AdHocDeclaration = {
        FunctionName: string;
        PredicateName: string;
        Variable: string;
        Template: TypeScheme;
        Instances: List<AdHocInstance>
    }

    type Declaration =
        | DFunction of name: string * fixedSizeParams: List<string> * body: Expression
        | DCheck of name: string * comparison: TypeScheme
        | DTag of name: string * tag: Type
        | DTest of name: string * left: Expression * right: Expression * testType: TestType
        | DAdhoc of AdHocInstance