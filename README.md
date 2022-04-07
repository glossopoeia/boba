# Boba

Boba is an early-stage, general purpose [concatenative](https://concatenative.org/) programming language featuring rich static types and type inference, in-line unit and property tests, algebraic effects, and a garbage-collected runtime. Boba programs can currently compile to C and Go backends, but both backends implement a bytecode for simplicity while native compilation is being investigated.

## Building from source

The Boba compiler is currently implemented in F#. Recommended to have both .NET 6 and Go language version 1.18 installed on the system before building. This repository is [Gitpod](https://gitpod.io/) compatible and will automatically create an image capable of building and running the compiler.

Example build-and-run command:

```
dotnet run --project Boba.Compiler compile test/while-expr
```

This will build the compiler, then `compile` the `test/while-expr.boba` file in the tests directory into an executable and then run it.

To use Boba's inline testing features, simply replace `compile` with `test`:

```
dotnet run --project Boba.Compiler test test/ackermann
```

This will run all the tests present in the `test/ackermann.boba` file and report on their success/failure.

## A Small but Powerful Core

The core language of Boba implements functions, algebraic effects via 'handlers', named algebraic datatypes with pattern matching, higher-order functions, extensible records and variants, fixed-size arrays, strings, numbers and numeric operations, and familiar branching and looping constructs.

The core is projected to eventually support 'runtime permissions' as a language feature.

Most other semantic features not listed above are defined as syntactic sugar in the Boba compiler front-end. A good example: in-line tests in Boba are just syntactic sugar for a pre-defined algebraic effect around a set of functions.