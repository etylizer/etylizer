# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

etylizer is a static typechecker for Erlang based on set-theoretic types. 
It can be used as a rebar3 plugin or as a standalone escript.

## Essential Commands

### Build and Development

```bash
make build             # Build the escript
```

### Testing

```bash
NO_INFER=1 rebar3 eunit -m tycheck_simple_tests                        # Run the test suite
rebar3 eunit -m tycheck_simple_tests                                   # Run the advanced test suite
NO_INFER=1 TEST=guards rebar3 eunit -m tycheck_simple_tests            # Run the test suite with just the guards.erl module
NO_INFER=1 TEST=guards:guards_01 rebar3 eunit -m tycheck_simple_tests  # Run the test suite with a single test case
```

### Running etylizer

There is a helper script `ety` which can be used with the --build flag to always
use the up to date version:

```bash
# Check a single file
./ety --build hello.erl

# Check a rebar project (must compile first with rebar3 compile)
./ety --build -P . -S src

# Debug mode (check only specific function with debug info)
./ety --build hello.erl --force -l debug -o foo/1

# Sanity check only (AST transformation without type checking)
./ety --build --sanity -I ./src ./src/*.erl
```

### Running a Single Test

Test files are in `test_files`. 

To test new features, running tests in `test_files/tycheck_simple` with infer disabled is enough.

Running tycheck simple tests:

For debugging, running etylizer directly is also efficient. 
E.g., just testing a single function `lc_14` in a given module:

```bash
./ety --build --no-deps -I include -f -l debug test_files/tycheck_simple/comprehension.erl -o lc_14
```

Log output until INFO will be printed to console.
The debug output will be written to `etylizer.log`. 

## Architecture

### Type-Checker Pipeline

1. **Parsing**: Uses Erlang's standard parser to create AST
2. **AST Transformation** (`ast_transform.erl`): Converts Erlang AST to internal representation with:
   - Unique local variable names
   - Resolved variable occurrences (new binding vs. reference)
   - Type definition bounds replaced by intersections
   - More features that are needed internally by the type checker (negation,
     intersection types, local recursive types)
3. **Sanity Checks** (`ast_check.erl`):
4. **Type Checking** (`typing.erl`, `typing_check.erl`, `typing_infer.erl`):
   - Generates constraints (`constr_gen.erl`)
   - Solves constraints (`constr_solve.erl`)
   - Uses set-theoretic constraint solving (`tally.erl`, `subty.erl`)
5. **Type Library** (`erlang_types`)
   - A set-theoretic types library that implements all necessary type operations
   - Implements constraint solving and subtyping operations on types
   - Needs its internal type representation, converting to and from `ast.erl` at
     the boundary

### Key Module Categories

**AST Processing:**
- `ast_erl.erl`: Erlang parser AST definitions
- `ast.erl`: Internal AST type definitions
- `ast_transform.erl`: Transforms Erlang AST to internal AST
- `ast_utils.erl`, `ast_lib.erl`: AST utilities

**Constraint System:**
- `constr.erl`: Constraint types
- `constr_gen.erl`: Constraint generation from code
- `constr_solve.erl`: Constraint solving
- `constr_simp.erl`: Constraint simplification
- `tally.erl`: Satisfiability checking and constraint solving via DNF type system

**Type System:**
- `subty.erl`: Subtyping relation
- `stdtypes.erl`: Standard Erlang types
- `symtab.erl`: Symbol table for types and functions
- `t.erl`: Type utilities
- `erlang_types/`: DNF-based type system implementation
  - `ty_node.erl`: Main type node interface
  - `ty_parser.erl`: Parses internal AST types to DNF types
  - `dnf_ty_*.erl`: DNF representations for specific type constructors
  - `etally.erl`: Constraint solving with the DNF type system

**Analysis Support:**
- `cm_*.erl`: Compilation manager (module interface, indexing, dependency graph)
- `parse.erl`, `parse_cache.erl`: File parsing and caching
- `errors.erl`: Error reporting
- `log.erl`: Logging framework

**External Dependencies:**
- `c_src/espresso/`: Espresso heuristic logic minimizer (used for DNF minimization in type system)

### Variable Scoping in AST Transformation

The AST transformation ensures all local variables have unique names and variable occurrences are properly resolved. 
This is critical for type checking. Pay special attention to scoping in:
- List comprehensions and generators
- Case expressions
- Function clauses
- Try/catch blocks

## Development Rules

- Every top-level function must have a type annotation
- Every module must have a short description at the top stating its purpose
- Complicated functions need documentation and unit tests
- Run the test suite with infer disabled first for efficiency
- Run the test suite with infer enabled if all tests pass
- NEVER run any git commands

## Codebase-Specific Notes

- The internal AST (defined in `ast.erl`) is simpler than Erlang's AST with guaranteed unique variable names and resolved references
- The type system uses a DNF (Disjunctive Normal Form) representation internally (`erlang_types/` directory)
- Constraint generation and solving are separate phases
- The symbol table (`symtab.erl`) tracks types, functions, and records across modules
- Caching is used extensively (`parse_cache.erl`) to avoid re-parsing unchanged modules
