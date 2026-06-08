defmodule StdlibSpecs do
  @moduledoc """
  Compare the two `map` functions both modules call internally:

      Erlang   :lists.map/2   -spec map(fun((A) -> B), [A]) -> [B].
      Elixir   Enum.map/2     @spec map(t(), (element() -> any())) :: list()

  Consequence: a precise return type cannot be derived from the Elixir spec
  alone. 
  """

  @spec increment_via_erlang([integer()]) :: [integer()]
  def increment_via_erlang(xs), do: :lists.map(fn x -> x + 1 end, xs)

  # See ../check.sh, which runs etylizer both ways so you can see the difference.
  @spec increment_via_elixir([integer()]) :: [integer()]
  def increment_via_elixir(xs), do: Enum.map(xs, fn x -> x + 1 end)

  # The same imprecision bites inside a pipe, which is how idiomatic Elixir is
  # usually written. Fails without the overlay; checks with it.
  @spec squares([integer()]) :: [integer()]
  def squares(xs), do: xs |> Enum.map(fn x -> x * x end)
end
