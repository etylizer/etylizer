# etylizer

![status badge](https://github.com/etylizer/etylizer/actions/workflows/erlang.yml/badge.svg)

Static typechecker for Erlang based on set-theoretic types.

## Benchmark Modifications

This is the version used for running the benchmarks for the IFL paper (TODO ref).

Modifications done for the paper version to the source code compared to the main branch:

* Instead of logging errors, the tool exits with these error codes immediately
  upon encountering the first error:
  * 1: type error
  * 2: not yet implemented
  * other: crash

### Type-checker pipeline

* Parse, using erlang's parser.
* Transform the AST into an internal representation. The AST for the internal representation
  is somewhat simpler and has the following properties:
  * All names of local variable are unique.
  * Variable occurences have been resolved so that we know whether a variable occurrence
    introduces a new binding or refers to an existing binding and in which module the existing
    binding is defined.
  * Bounds in type definitions have been replaced by intersections.
* Perform several sanity checks
  * Check that type defs are regular and contractive. This requires constructing a dependency
    cycle and potentially loading of type defs from other modules.
  * Check that we have a type signature for all non-local functions. This requires loading
    type specs from external modules. We also need type spec for all bifs and for all
    erlang modules.
  * Check that each top-level functions have a type spec.

