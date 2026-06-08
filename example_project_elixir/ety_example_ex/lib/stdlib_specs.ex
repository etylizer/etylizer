defmodule StdlibSpecs do
  @moduledoc """
  The headline of this example: **Elixir's standard-library typespecs are far
  less precise than Erlang's**, and that directly limits what a type checker can
  prove — through no fault of the user's code.

  Compare the two `map` functions both modules call internally:

      Erlang   :lists.map/2   -spec map(fun((A) -> B), [A]) -> [B].
      Elixir   Enum.map/2     @spec map(t(), (element() -> any())) :: list()

  The Erlang spec is *parametric*: the element types `A` and `B` flow through
  it, so a caller's element type is preserved in the result. The Elixir spec
  throws that information away — it takes an opaque `Enumerable.t()` and a
  function returning `any()`, and promises only a bare `list()` (i.e.
  `[any()]`) — even though at runtime `Enum.map/2` on a list behaves exactly
  like `:lists.map/2`.

  Consequence: a precise return type *cannot* be derived from the Elixir spec
  alone. The two functions below are the same computation, but only the
  Erlang-backed one type checks out of the box.
  """

  # Uses Erlang's polymorphic `:lists.map/2`. etylizer pulls the precise spec
  # straight from OTP's stdlib and proves the result is exactly `[integer()]`.
  # This ALWAYS type checks.
  @spec increment_via_erlang([integer()]) :: [integer()]
  def increment_via_erlang(xs), do: :lists.map(fn x -> x + 1 end, xs)

  # Identical logic via Elixir's `Enum.map/2`. Because the stdlib spec returns a
  # bare `list()`, etylizer cannot prove the result is `[integer()]`:
  #
  #   * WITHOUT an overlay        -> TYPE ERROR (this is the point of the example)
  #   * WITH overlays/elixir_overlay.erl, which restores a precise spec
  #         'Elixir.Enum:map'([A], fun((A) -> B)) -> [B]
  #     -> type checks
  #
  # See ../check.sh, which runs etylizer both ways so you can see the difference.
  @spec increment_via_elixir([integer()]) :: [integer()]
  def increment_via_elixir(xs), do: Enum.map(xs, fn x -> x + 1 end)

  # The same imprecision bites inside a pipe, which is how idiomatic Elixir is
  # usually written. Fails without the overlay; checks with it.
  @spec squares([integer()]) :: [integer()]
  def squares(xs), do: xs |> Enum.map(fn x -> x * x end)
end
