# etylizer

![status badge](https://github.com/etylizer/etylizer/actions/workflows/erlang.yml/badge.svg)

Static typechecker for Erlang based on set-theoretic types.

## User-level documentation

Yet to come...

## Developer documentation

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

### Rules of hacking

* Make sure every top-level function has a type annotation.
* Make sure every module has a short description at the top of the file
  stating the purpose of the module.
* Make sure that complicated functions have a short text of documentation.
* Make sure that complicated functions have unit tests.
* Make sure that all unit tests are running before comitting: `make test`
* Make sure the dialyzer is happy before comitting: `make check`
