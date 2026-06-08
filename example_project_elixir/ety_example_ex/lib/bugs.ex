defmodule Bugs do
  @moduledoc """
  Deliberate type errors — etylizer reports each one. Several are distilled from
  common mistakes in student exercise solutions.

  These fail *with* the overlay too: they are real bugs in the code's types, not
  gaps in stdlib specs. Compare with `StdlibSpecs`, whose "failure" disappears
  once the overlay supplies a precise spec.
  """

  # The spec promises the result is `false`, but the first clause returns `true`.
  # (A real solution wrote `:: false` where it meant `:: boolean()`.)
  @spec same?(any(), any()) :: false
  def same?(x, x), do: true
  def same?(_, _), do: false

  # A pipe that yields a *list* where the spec promises a single integer.
  @spec total([integer()]) :: integer()
  def total(xs), do: xs |> :lists.map(fn x -> x + 1 end)

  # Forgot to wrap the result in a list.
  @spec wrap(a) :: [a] when a: var
  def wrap(x), do: x

  # Returns the integer argument where an atom is promised.
  @spec label(integer()) :: atom()
  def label(n), do: n
end
