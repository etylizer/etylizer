# etylizer

![status badge](https://github.com/etylizer/etylizer/actions/workflows/erlang.yml/badge.svg)
[![ICFP26](https://img.shields.io/badge/ICFP-26-blue)](https://doi.org/10.1145/3828708)
[![Erlang26](https://img.shields.io/badge/Erlang_Workshop-26-blue)](https://doi.org/10.1145/3830434.3830945)

Static typechecker for Erlang based on set-theoretic types.

Try the [playground](https://albsch.github.io/etylizer-editor/) to see how etylizer works for Erlang and Elixir code.

This is the **experimental** (`experimental`) branch.

**Branches.**

* `main`: the stable release; always has the most up-to-date bug fixes.
* `dev`: not-yet-approved optimizations and community-approved to-be-tested features.
  * [improved compilation manager](https://github.com/etylizer/etylizer/pull/342)
  * [bit string and binary support](https://github.com/etylizer/etylizer/pull/330).
  * [Erlang message types](https://github.com/etylizer/etylizer/pull/358)
* `experimental`: novel type-level features to try out.
  * [nominal types](https://github.com/etylizer/etylizer/pull/338).

## User-level documentation

User-level documentation is work in progress.

Currently supported 

* native build
* [LSP](https://github.com/albsch/erlang-language-platform) (fork of
  [ELP](https://github.com/WhatsApp/erlang-language-platform))

### Native Build

* `make` or `rebar3 escriptize` will generate a standalone portable escript called `etylizer` inside the directory
  `_build/default/bin`
* `etylizer -h` for help
  * if etylizer is not on the current path, then prepend the folder where etylizer is located: `$PATH_TO_ETYLIZER/etylizer -h`
* To check a single module file `hello.erl` execute `etylizer hello.erl`
* To check a rebar project `hello.erl`
    * compile the project (e.g. `rebar3 compile`)
    * execute `etylizer -P . -S src` while in the root of the project

Useful for debugging:

    etylizer hello.erl --force -l debug -o foo/1

* type checks only the function `foo/1` (`-o`) with additional debug information
  (`-l`)
* disables caching of results, i.e. force type checking (`--force`)
* sets the verbosity of logging to `debug`

There are two self-contained example projects to showcase native usage.

* [`example_project/`](example_project). A simple Erlang project. A tour of etylizer features
  (occurrence typing, intersection types, exhaustiveness checks, ...).
* [`example_project_elixir/`](example_project_elixir). A simple Elixir project.

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
  * It is stable and is used for caching.
* Perform several sanity checks
  * Check that type defs are regular and contractive. This requires constructing a dependency
    cycle and potentially loading of type defs from other modules.
  * Check that we have a type signature for all non-local functions. This requires loading
    type specs from external modules. We also need type spec for all bifs and for all
    erlang modules.
  * Check that each top-level functions have a type spec.
* Generate constraint sets
* Solve them via `erlang_types` tallying.
* On error, try to locate the error location within a reasonable timeframe.

### Rules of hacking

* Make sure every top-level function has a type annotation.
* Make sure every module has a short description at the top of the file
  stating the purpose of the module.
* Make sure that complicated functions have a short text of documentation.
* Make sure that complicated functions have unit tests.
* Make sure that all unit tests are running before comitting: `make test`
* Make sure the etylizer and dialyzer is happy before comitting: `make check`
