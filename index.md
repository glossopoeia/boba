## Concatenative made Comfortable

Boba intends to be a high-level, general purpose concatenative programming language focused on composability of functions and data. The language is early stage and should be used with caution while the implementation comes together!

### Notable Language Feature Highlights

NOTE: *Some of the following are planned - i.e. not yet implemented!*

- Left-to-right syntactic execution order
- Multiple return values with zero headache
- Language-level programmer support
    - Unit & property tests
    - Inline markdown documentation
- Some batteries included
    - Async io & sockets
    - Threading
    - Native SDL support
- Robust algebraic effect semantics
    - Effect parameters
    - Multiple resume
    - Injection
- Type inference for advanced type features
    - Type classes with functional dependencies (extended by custom CHR rules, i.e. some support for programmer directed type-inference)
    - Uniqueness types supporting in-place update operations on some data structures
    - Function totality checking/marking
    - Units of measure
    - Parametric compile-time sized collections
    - Permission types marking system permissions required by some functions

### Feature Buzz-word Checklist

- First class functions ✔️
- Statically typed ✔️
- Compiled ✔️
- Garbage collected ✔️
- Object oriented ❌
- Lazy evaluation ❌
- Macro system ❌
- Low-level ❌

### Examples

*hailstone.boba*
```
// Examples of stack combinators. Because Boba supports variables,
// it is trivial to define new stack shuffle words in Boba, but also
// not entirely necessary. Choose whichever you're more comfortable with.
func drop n =
func swap n m = m n
func dup x = x x

func dec = 1 swap sub-isize
func is-even n = 2 n divreme-isize drop 0 eq-isize

// This is a Boba-implementation of the hailstone function from the
// Collatz conjecture. It demonstrates lists, branching, integer math,
// recursion, and variable scopes.
rec func hailstone n =
    switch {
        n 1 eq-isize => list [];
        n is-even => {
            let rem quot = 2 n divreme-isize;
            quot hailstone
        }
        else => 3 n mul-isize 1 add-isize hailstone
    }
    n cons-list

// These are examples of the built-in testing mechanism for Boba,
// shamelessly inspired by those of Pyret.
test hailstone-1 = 1 hailstone is [1]
test hailstone-2 = 2 hailstone is [2, 1]
test hailstone-3 = 3 hailstone is [3, 10, 5, 16, 8, 4, 2, 1]
test hailstone-6 = 6 hailstone is [6, 3, 10, 5, 16, 8, 4, 2, 1]
```

*amb.boba*
```
// Example effect-set declaration. These will included types of each
// effect handler later on.
effect amb! {
    flip!
}

// This example demonstrates an effect handler that resumes more than
// once. `flip!` is used in the handled expression to build up a list
// containing the `xor` operation truth table results. `main` is the
// entry point for applications, and in this example `main` takes no
// parameters and leaves a list on the stack when it returns. This
// may not be allowed once type inference works properly, but this
// example currently does work in the Boba compiler.
main =
    handle {
        flip! flip! xor-bool
    } with {
        flip! => {
            let x = false resume;
            let y = true resume;
            x y append-list
        };
        after v => nil-list v cons-list;
    }
```

### Compiler Suite Usage

Coming soon! The Boba compiler is currently implemented in F# while the language grows to it's initial versions, and requires .NET 6.0. The interface is highly unstable right now and likely to change rapidly as more features are added.

Boba depends on [MochiVM](https://github.com/robertkleffner/MochiVM) for it's runtime. MochiVM is being developed concurrently alongside Boba as a virtual machine supporting statically typed concatenative languages. As such, it is also in a period of instability while initial development proceeds.

### Feedback

Questions, concerns, or ideas? Feel free to start a discussion in this repository!
