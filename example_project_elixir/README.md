# Elixir example project

This is the Elixir counterpart to [`../example_project`](../example_project). It
shows that etylizer can type check **Elixir** code, and it highlights a real
limitation that has nothing to do with etylizer: **Elixir's standard-library
typespecs are much less precise than Erlang's.**

## How etylizer checks Elixir

etylizer type checks the **compiled** BEAM output, not the `.ex` source. The
Elixir compiler stores Erlang abstract forms — including the `@spec`s — in each
module's `debug_info` chunk, and etylizer reads them from there. So the workflow
is just:

1. `mix compile` your project.
2. Point etylizer at the resulting `Elixir.*.beam` files, adding Elixir's `ebin`
   to the search path with `-a` (it holds `elixir_erl`, the backend that decodes
   the debug_info, plus the stdlib BEAMs that calls resolve against).

## Run it

```bash
./check.sh
```

Requires `elixir`/`mix` on your `PATH`. The script compiles the project and runs
etylizer twice — once without the Elixir overlay and once with it.

## What it shows

### `lib/showcase.ex` — capabilities

A short tour of things etylizer *proves* about ordinary Elixir code using
set-theoretic types: unions and occurrence typing, intersection (overloaded)
specs, parametric polymorphism (`when a: var`), precise tuple/list types, and
distributivity of unions over tuples. Every function here type checks.

### `lib/elixir_syntax.ex` — Elixir-specific syntax

etylizer checks the *compiled* BEAM, i.e. the code *after* Elixir has desugared
its surface syntax into ordinary Erlang forms. So Elixir-specific constructs are
checked "for free" once they reduce to plain calls/cases/binaries:

* the **pipe** operator `x |> f() |> g()` (becomes `g(f(x))`),
* the **capture** operator `&(&1 + 1)` (becomes `fn x -> x + 1 end`),
* **`with`** (becomes nested `case`s),
* **string interpolation** (becomes a binary), and
* **default arguments** `def scale(xs, factor \\ 2)` — Elixir generates a
  spec-less `scale/1`, and etylizer's BEAM reader *synthesizes* its spec by
  dropping the defaulted parameter from `scale/2`'s spec.

Every function here type checks.

### `lib/stdlib_specs.ex` — the headline: Elixir's stdlib specs are weak

Both functions below are the *same computation*. The only difference is which
standard library's `map` they call:

```elixir
def increment_via_erlang(xs), do: :lists.map(fn x -> x + 1 end, xs)   # OK
def increment_via_elixir(xs), do: Enum.map(xs, fn x -> x + 1 end)     # type error (without overlay)
```

Why does one fail? Compare the specs:

| | spec | polymorphic? |
|---|---|---|
| Erlang `:lists.map/2` | `fun((A) -> B), [A]) -> [B]` | ✅ element types flow through |
| Elixir `Enum.map/2` | `(t(), (element() -> any())) :: list()` | ❌ returns a bare `list()` |

Elixir's spec takes an opaque `Enumerable.t()` and a function returning `any()`,
and promises only `list()` (i.e. `[any()]`). The element type is discarded —
even though, on a list, `Enum.map/2` behaves exactly like `:lists.map/2`. So a
checker simply cannot prove `increment_via_elixir/1` returns `[integer()]` from
the Elixir spec alone; `increment_via_erlang/1`, backed by Erlang's parametric
spec, checks out of the box.

This is pervasive across `Enum`, `List`, `Map`, `Stream`, … — the specs are
written for documentation and Dialyzer's success typing, not for precise
checking, so they routinely collapse to `list()` / `map()` / `any()`.

### The workaround: overlays

etylizer lets you supply more precise specs for external functions via an
*overlay*. [`../overlays/elixir_overlay.erl`](../overlays/elixir_overlay.erl)
restores parametric specs for the common `Enum`/`List`/`Tuple` functions, e.g.

```erlang
-spec 'Elixir.Enum:map'([A], fun((A) -> B)) -> [B];
                        (#{K => V}, fun(({K, V}) -> R)) -> [R].
```

Pass it with `--type-overlay`, and `increment_via_elixir/1` type checks. The
second pass in `check.sh` does exactly this — same code, same BEAM, now green.

### `lib/bugs.ex` — type errors etylizer catches

A handful of deliberate type errors, several distilled from real student
exercise solutions, e.g.

```elixir
@spec same?(any(), any()) :: false   # spec says false ...
def same?(x, x), do: true            # ... but this returns true  -> type error
```

The crucial contrast with `stdlib_specs.ex`: these are *real* bugs in the code's
types, so they fail **with the overlay too**. The overlay restores precision the
stdlib threw away; it does not paper over genuine mistakes. In `check.sh` you can
see the `StdlibSpecs` errors disappear on the second (overlay) pass while every
`Bugs` error stays put.

## The four modules at a glance

| module | what it demonstrates | result |
|---|---|---|
| `Showcase` | set-theoretic type-system features | all check |
| `ElixirSyntax` | pipes, captures, `with`, interpolation, default args | all check |
| `StdlibSpecs` | Elixir stdlib specs are weaker than Erlang's | fail → **pass with overlay** |
| `Bugs` | real type errors (student-style) | fail (overlay does *not* help) |
