# etylizer

![status badge](https://github.com/etylizer/etylizer/actions/workflows/erlang.yml/badge.svg)

Static typechecker for Erlang based on set-theoretic types.

## User-level documentation

### Install
Add this to your `rebar.config` file:
```erlang
{plugins, [
    {rebar3_etylizer, {git, "https://github.com/etylizer/rebar3_etylizer.git"}}
]}.
```

Then run:
```
rebar3 etylizer
```

For a full list of plugin options see the [rebar plugin repo](https://github.com/etylizer/rebar3_etylizer).

### Build

* `make` or `rebar3 escriptize` will generate a standalone portable escript called `etylizer` inside the directory
  `_build/default/bin`
* `etylizer -h` for help
  * if etylizer is not on the current path, then prepend the folder where etylizer is located: `$PATH_TO_ETYLIZER/etylizer -h`
* To check a single module file `hello.erl` execute `etylizer hello.erl`
* To check a rebar project `hello.erl`
    * compile the project (e.g. `rebar3 compile`)
    * execute `etylizer -P . -S src` while in the root of the project

Useful for debugging:

    etylizer hello.erl --force -l debug -o foo1/1

* type checks only the function `foo/1` (`-o`) with additional debug information
  (`-l`)
* disables caching of results, i.e. force type checking (`--force`)

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
