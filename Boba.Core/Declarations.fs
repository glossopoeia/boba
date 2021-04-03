namespace Boba.Core

module Declarations =

    open Expression
    open Kinds
    open Types

    type TestType =
        | TTIsRoughly
        | TTSatisfies
        | TTViolates
        | TTIs of Expression
        | TTIsNot of Expression

    type Test = { Name: string; Expected: Expression; Actual: Expression; Type: TestType }

    type Property = { Name: string; Params: List<string>; Expected: Expression; Actual: Expression; Type: TestType }



    type TypeclassInstance = {
        Overloaded: QualifiedType;
        Body: Map<string, Expression>;
    }

    type TypeclassMethod = {
        Signature: Option<TypeScheme>
        Default: Option<Expression>
    }

    type Typeclass = {
        PredicateName: string;
        Variable: string;
        Superclasses: List<string>
        Methods: Map<string, TypeclassMethod>
        Instances: List<TypeclassInstance>
        Laws: Map<string, Property>
    }



    type Effect = {
        Name: string;
        TypeParams: List<(string * Kind)>
        Operations: Map<string, TypeScheme>
    }



    type Constructor = {
        Name: string;
        Elements: List<Type>
    }



    type Function = {
        Name: string;
        FixedSizeParams: List<string>;
        Body: Expression
    }



    let instanceDefName adhocFullName instType =
        $"${adhocFullName}_{instType}"

    type Declaration =
        | DData of name: string * typeParams: List<string * Kind>
        | DConstructor of Constructor
        | DFunction of Function
        | DCheck of name: string * comparison: TypeScheme
        | DTag of name: string * tag: Type
        | DTest of Test
        | DProperty of Property
        | DTypeclass of Typeclass

    type Program = { Main: Expression; Declarations: Map<string, Declaration> }