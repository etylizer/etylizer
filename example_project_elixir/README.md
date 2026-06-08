# Elixir example project

This is the Elixir counterpart to [`../example_project`](../example_project). 
Etylizer can type check **Elixir**, too.

## How etylizer checks Elixir

etylizer type checks the **compiled** BEAM output, not the `.ex` source. 
The Elixir compiler stores Erlang abstract forms (including `@spec`s) in each
module's `debug_info` chunk, and etylizer reads them from there. 
So the workflow is:

1. `mix compile` your project
2. Point etylizer at the resulting `Elixir.*.beam` files, adding Elixir's `ebin`
   to the search path with `-a`

## Run it

```bash
./check.sh
```

Requires `elixir`/`mix` on your `PATH`. The script compiles the project and runs
etylizer twice, once without the Elixir overlay and once with it.


## `lib/showcase.ex` capabilities

Similar to the Erlang project.


## `lib/elixir_syntax.ex` Elixir-specific syntax

etylizer checks the *compiled* BEAM, i.e. the code *after* Elixir has desugared its surface syntax into ordinary Erlang forms. 
The syntax covers, among others:

* **pipes** `x |> f() |> g()` (becomes `g(f(x))`) and **captures** `&(&1 + 1)`
  / `&fun/1` (become `fn`),
* **conditionals**: `case`, `if`/`unless`, **`cond`**, `with`, `try`/`rescue`,
  and multi-clause anonymous `fn`,
* **operators**: arithmetic, the strict booleans `and`/`or`/`not`, the
  short-circuit `&&`/`||`/`!`, comparisons, `<>`, `++`/`--`, `in`,
* **pattern matching**: the pin `^`, nested destructuring, and map patterns,
* **data literals**: tuples, lists/cons, keyword lists, maps and map-update,
  binary *construction*, and sigils (`~c`, `~w`, `~s`),
* **string interpolation**, `for` comprehensions, **default arguments**
  `def scale(xs, factor \\ 2)` (Elixir generates a spec-less `scale/1`, and
  etylizer's BEAM reader *synthesizes* its spec from `scale/2`), and `__MODULE__`.


## Pitfalls

This is just a prototype and has still some rough edges.

**Generated dead branches.** 
`cond`, the strict `and`/`or`, and string interpolation each desugar to a `case` with a compiler-generated defensive branch. 
Under a precise spec those branches are provably dead, but the programmer never wrote them. 

* [x] Etylizer skips redundancy reporting on branches the compiler marked `generated`.

**structs, `%S{}`, maps.** 

* [ ] Better support for maps

**Precise binary support** 

* [ ] Depends on precise binary types (#330)


## `lib/stdlib_specs.ex` Elixir's stdlib specs

**Protocols and stdlib specs** 
Both functions below are the same computation and
the only difference is which standard library's `map` they call:

```elixir
def increment_via_erlang(xs), do: :lists.map(fn x -> x + 1 end, xs)   # OK
def increment_via_elixir(xs), do: Enum.map(xs, fn x -> x + 1 end)     # type error (without overlay)
```

* [ ] Think about protocol support 


## Type overlays 

etylizer lets you supply more precise specs for external functions via an *overlay*. 
[`../overlays/elixir_overlay.erl`](../overlays/elixir_overlay.erl) restores parametric 
specs for the common `Enum`/`List`/`Tuple` functions, e.g.

```erlang
-spec 'Elixir.Enum:map'([A], fun((A) -> B)) -> [B];
                        (#{K => V}, fun(({K, V}) -> R)) -> [R].
```

Pass it with `--type-overlay`, and `increment_via_elixir/1` type checks. 
The second pass in `check.sh` does this.

### `lib/bugs.ex`

A handful of deliberate type errors, 
