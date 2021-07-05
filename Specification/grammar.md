A program is composed of units. A unit is a file containing import statements referencing other units, an ordered-list of declarations, and either an export clause or a program entry point named 'main'.

Every executable program must have at exactly one unit containing a 'main' entry point. However, when using test mode, the compiler may be run on any unit, and the tests for that unit will be evaluated and the success/failure results displayed for the developer.

```
program ::= unit*

unit ::= import* declaration* (export | main)
```

The entry point 'main' looks much like a standard function definition; it is somewhat condensed, may not have fixed-size parameters, and must be named 'main'. 'main' may not be used as the name for any other definition; hence 'main' is reserved as a keyword.

An export list may contain a set of (optionally qualified) names. These names that may be included should reference *term-level* declarations, e.g. functions, constructors, constructor tests, and effect operations. *Type-level* declarations are always exported, and some term-level declarations, such as typeclass instances, are also always exported.

```
main ::= "main" "=" term-expr
export ::= "export" "{" name-list "}"
```

Import clauses allow a unit to reference the term- and type-level declarations in other units. `import-everything` brings all names of the imported module into scope in the importing module; use with caution. Qualified `import` clauses allow an optional list of selected names to bring into the scope of the importing module without need for qualification.

Remote units can be pulled from a set of known unit repositories. They are denoted by organization, project, and unit name, along with the major, minor, and patch semantic version numbers.

```
import ::= "import" "as" SMALL_NAME "from" (STRING | remote) 
         | "import" "as" SMALL_NAME "{" name-list "}" "from" (STRING | remote)
         | "import-everything" "from" (STRING | remote)

remote ::= SMALL_NAME "." SMALL_NAME "." SMALL_NAME ":" NATURAL "." NATURAL "." NATURAL
```

```
declaration
    ::= data-decl
      | data-rec-decl
      | pattern-decl
      | typeclass-decl
      | instance-decl
      | deriving-decl
      | rule-decl
      | effect-decl
      | tag-decl
      | alias-decl
      | check-decl
      | test-decl
      | law-decl
      | func-decl
      | func-rec-decl
```

```
data-decl ::= "data" BIG_NAME type-var-decl* "=" (ctor-decl ("|" ctor-decl)*)?

data-rec-decl ::= "rec" data-decl
                | "rec" "{" data-decl+ "}"

ctor-decl ::= BIG_NAME type-expr*
```

```
pattern-decl ::= "pattern" BIG_NAME term-var* "=" pattern-expr
```

```
typeclass-decl ::= "class" BIG_NAME type-var-decl* "=" 
```