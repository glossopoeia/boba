# Boba - A Structured Concatenative Language

Boba is an early-stage, general purpose [concatenative](https://concatenative.org/) programming language.

Key features include:
1. Expressive, mostly implicit static types and kinds
2. Language-incorporated unit and property tests + runners
3. Algebraic effects via scoped effect handlers
4. Algebraic data types and pattern matching on constructors
5. Compile-time resolved function overloading
6. Structurally typed tuples, records and variants
8. Byte-code VM-in-Go backend with straight-forward first-order FFI access
9. Familiar looping, branching, and variable definition syntax constructs

## Hailstone Example

```
func is-even n = n 2 rem-i32 0 eq-i32

about :
> The `hailstone` function is sometimes named that because of how the values
> 'bounce' up and down (like hail in a storm cloud) as the sequence computes.

rec func hailstone n =
    switch {
        | n 1 eq-i32 => []
        | n is-even  => n 2 div-i32 hailstone
        | else       => 3 n mul-i32 inc-i32 hailstone
    }
    n cons-list

test hailstone-1? = 1 hailstone is [1]
test hailstone-2? = 2 hailstone is [1, 2]
test hailstone-3? = 3 hailstone is [1, 2, 4, 8, 16, 5, 10, 3]
test hailstone-6? = 6 hailstone is [1, 2, 4, 8, 16, 5, 10, 3, 6]

export { hailstone }
```

See the `test/` folder for many more examples of Boba syntactic and semantic features.

## Building from source

The Boba compiler is currently implemented in F#. Recommended to have both .NET 6 and Go language version 1.18 installed on the system before building. This repository is [Gitpod](https://gitpod.io/) compatible and will automatically create a container capable of building and running the compiler.

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

To run a test or program without the current runtime debug trace, include a `release` flag:

```
dotnet run --project Boba.Compiler test test/hailstone release
```

## Installation

Installers and binary packages are not yet available while the compiler CLI further stabilizes.

## License

Boba is available and distributed under the terms of the MIT license. See LICENSE for details.

## Roadmap

In no particular order, and missing some potential work that may take priority:

- Ecosystem feature: Flesh-out primitives library further
- Codegen feature: Compile some Boba functions to Go rather than byte-code
- Language feature: Pattern alias declarations
- Language feature: Improved overload instance syntax
- Language feature: `for` loops over standard iterators