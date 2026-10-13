defmodule ElixirSyntax do
  @moduledoc """
  A tour of Elixir surface syntax, one construct per function, each with a
  `@spec` that etylizer checks.

  Everything here type checks. A few constructs need `overlays/elixir_overlay.erl`
  because Elixir compiles them to calls etylizer has no precise
  spec for.

  Constructs etylizer does NOT yet handle are listed at the bottom of the file.
  """

  ## ----- Pipes, captures, anonymous functions -----

  # `|>` desugars to nested calls: `x |> inc() |> double()` == `double(inc(x))`.
  @spec inc_then_double(integer()) :: integer()
  def inc_then_double(x), do: x |> inc() |> double()

  @spec inc(integer()) :: integer()
  defp inc(x), do: x + 1

  @spec double(integer()) :: integer()
  defp double(x), do: x * 2

  # The capture `&(&1 + 1)` is exactly `fn x -> x + 1 end`.
  @spec add_one_all([integer()]) :: [integer()]
  def add_one_all(xs), do: :lists.map(&(&1 + 1), xs)

  # Capturing a named function: `&double/1` is `fn x -> double(x) end`.
  @spec double_all([integer()]) :: [integer()]
  def double_all(xs), do: :lists.map(&double/1, xs)

  # A multi-clause anonymous `fn` becomes a multi-clause function value; applying
  # it with `.()` is a normal call whose clauses etylizer checks for coverage.
  @spec is_zero(integer()) :: atom()
  def is_zero(x), do: (fn 0 -> :zero; _ -> :nonzero end).(x)

  ## ----- Conditionals -----

  # `case` is the primitive everything else desugars into.
  @spec classify(integer()) :: atom()
  def classify(x) do
    case x do
      0 -> :zero
      n when n > 0 -> :pos
      _ -> :neg
    end
  end

  # `if`/`else` desugars to a boolean `case`. Both arms are live, so it checks.
  @spec clamp(integer()) :: integer()
  def clamp(x), do: if(x < 0, do: 0, else: x)

  # `unless` is `if` with the arms swapped.
  @spec at_least_one(boolean()) :: integer()
  def at_least_one(b), do: unless(b, do: 1, else: 2)

  # `cond` desugars to *nested* `case`s ending in a generated
  # `false -> raise CondClauseError` branch. With a final `true ->` that branch
  # is statically dead; etylizer skips redundancy reporting on compiler-generated
  # branches, so this checks cleanly.
  @spec sign(integer()) :: atom()
  def sign(x) do
    cond do
      x > 0 -> :pos
      x < 0 -> :neg
      true -> :zero
    end
  end

  # `with` desugars to nested `case`s; the `else` clause makes the match total.
  @spec first_two([a]) :: {:ok, a, a} | :error when a: var
  def first_two(list) do
    with [x | rest] <- list,
         [y | _] <- rest do
      {:ok, x, y}
    else
      _ -> :error
    end
  end

  # `try`/`rescue` desugars to a `try` form; the rescue clause provides the
  # alternative result type.
  @spec safe_div(integer(), integer()) :: integer()
  def safe_div(a, b) do
    try do
      div(a, b)
    rescue
      ArithmeticError -> 0
    end
  end

  ## ----- Operators -----

  # Arithmetic operators stay as Erlang operator nodes (`+`, `-`, `*`, `div`).
  @spec arith(integer(), integer()) :: integer()
  def arith(a, b), do: a * b + 1 - div(a, 2)

  # Strict boolean operators `and`/`or`/`not` REQUIRE booleans: they compile to a
  # `case` with a generated `_ -> raise BadBooleanError` arm. Under the boolean
  # spec that arm is dead, and (being compiler-generated) it is exempt from
  # redundancy reporting.
  @spec both_or_neither(boolean(), boolean()) :: boolean()
  def both_or_neither(a, b), do: (a and b) or not a

  # Short-circuit `&&`/`||`/`!` accept any truthy value and return one of their
  # operands.
  @spec positive_or_zero(integer()) :: integer()
  def positive_or_zero(x), do: (x > 0 && x) || 0

  # Comparison operators yield a boolean.
  @spec in_order?(integer(), integer()) :: boolean()
  def in_order?(a, b), do: a <= b

  # `<>` concatenates binaries. (Its other use, prefix *matching*
  # `"hello " <> rest`, needs precise binary types)
  @spec shout(String.t()) :: String.t()
  def shout(s), do: s <> "!"

  # `++` and `--` are compiled to erlang:'++'/2 and erlang:'--'/2 calls; the
  # overlay supplies their polymorphic specs (see elixir_overlay.erl).
  @spec append([a], [a]) :: [a] when a: var
  def append(xs, ys), do: xs ++ ys

  # `in` membership test.
  @spec small?(integer()) :: boolean()
  def small?(x), do: x in [1, 2, 3]

  ## ----- Pattern matching -----

  # `^x` pins an existing binding instead of rebinding it.
  @spec same?(integer(), integer()) :: atom()
  def same?(x, y) do
    expected = x
    case y do
      ^expected -> :equal
      _ -> :different
    end
  end

  # Nested destructuring in a function head.
  @spec sum_nested({integer(), {integer(), integer()}}) :: integer()
  def sum_nested({a, {b, c}}), do: a + b + c

  ## ----- Data literals -----

  # Tuple and list/cons constructors.
  @spec pair_with(integer(), [integer()]) :: {{integer(), integer()}, [integer()]}
  def pair_with(x, xs), do: {{x, x}, [x | xs]}

  # Keyword lists are just lists of `{atom, value}` pairs.
  @spec defaults() :: keyword()
  def defaults(), do: [retries: 3, timeout: 5]

  # Maps. etylizer supports open map types (`optional(...)`), so we spec maps
  # that way rather than with mandatory `%{a: integer()}` keys.
  @spec wrap(integer()) :: %{optional(atom()) => integer()}
  def wrap(x), do: %{a: x, b: x}

  # Map update syntax `%{m | k => v}` requires the key to already exist.
  @spec bump_a(%{optional(atom()) => integer()}) :: %{optional(atom()) => integer()}
  def bump_a(m), do: %{m | a: 5}

  # Matching a map pattern extracts a known key.
  @spec get_a(%{optional(atom()) => integer()}) :: integer() | nil
  def get_a(%{a: v}), do: v
  def get_a(_), do: nil

  # Binary construction. (Binary *pattern matching* across clauses — e.g.
  # `<<b, rest::binary>>` vs `<<>>` — needs precise binary types; see the note.)
  @spec tag_byte(binary()) :: binary()
  def tag_byte(b), do: <<0, b::binary>>

  ## ----- Sigils -----

  # `~c` is a charlist, `~w` a word list, `~s` a string. (`~r`, `~D` etc. build
  # structs — see the limitations note below.)
  @spec a_charlist() :: charlist()
  def a_charlist(), do: ~c"hello"

  @spec words() :: [String.t()]
  def words(), do: ~w(alpha beta gamma)

  @spec greeting() :: String.t()
  def greeting(), do: ~s"hello world"

  ## ----- Comprehensions, interpolation, defaults, module ref -----

  # A `for` comprehension over a single list generator. Elixir optimizes this
  # form straight into `Enum.map/2`, so it inherits the imprecise `Enum.map`
  # spec (see stdlib_specs.ex) and needs the overlay to recover `[integer()]`.
  @spec increments([integer()]) :: [integer()]
  def increments(xs), do: (for x <- xs, do: x + 1)

  # String interpolation `"...#{e}..."` compiles to a binary built from a
  # generated `is_binary`-fast-path `case`; the non-binary fallback is dead under
  # `String.t()` and (being generated) is exempt from redundancy reporting.
  @spec greet(String.t()) :: String.t()
  def greet(name), do: "Hello, #{name}!"

  # Default arguments: Elixir generates `scale/1` (calling `scale/2` with the
  # default) with no spec of its own. etylizer's BEAM reader synthesizes that
  # spec by dropping the defaulted parameter from `scale/2`, so both arities check.
  @spec scale([integer()], integer()) :: [integer()]
  def scale(xs, factor \\ 2), do: :lists.map(fn x -> x * factor end, xs)

  # `__MODULE__` is replaced at compile time by the module atom.
  @spec me() :: module()
  def me(), do: __MODULE__

  ## ----- Not yet supported by etylizer (compile fine, fail to check) -----
  #
  #   * Structs / `defstruct` / `%Struct{}` and the Range literal `1..10`:
  #     these are maps with mandatory keys (including `__struct__`), and
  #     etylizer does not support mandatory map associations in specs yet.
  #   * Dynamic access `map[:key]`
  #   * `for` with filters or multiple generators (the comprehension lowers to
  #     an accumulator fold whose element type etylizer cannot yet track).
  #   * Binary *pattern matching* across clauses (`<<b, rest::binary>>` vs `<<>>`,
  #     or `"prefix" <> rest`). On this base every binary collapses to a single
  #     bitstring type, so a follow-up binary clause looks redundant.
end
