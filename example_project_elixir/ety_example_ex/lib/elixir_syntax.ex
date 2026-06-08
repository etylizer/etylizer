defmodule ElixirSyntax do
  @moduledoc """
  etylizer checks Elixir by reading the *compiled* BEAM — that is, *after* the
  Elixir compiler has desugared its surface syntax into ordinary Erlang forms.
  So a lot of Elixir-specific syntax is checked "for free": it reduces to plain
  calls, `case`s and binaries that etylizer already understands. Every function
  here type checks.
  """

  # The pipe operator `|>` desugars to nested calls: `x |> inc() |> double()`
  # becomes `double(inc(x))`, checked like any other call chain.
  @spec inc_then_double(integer()) :: integer()
  def inc_then_double(x), do: x |> inc() |> double()

  @spec inc(integer()) :: integer()
  defp inc(x), do: x + 1

  @spec double(integer()) :: integer()
  defp double(x), do: x * 2

  # The capture operator `&`: `&(&1 + 1)` is just `fn x -> x + 1 end`.
  @spec add_one_all([integer()]) :: [integer()]
  def add_one_all(xs), do: :lists.map(&(&1 + 1), xs)

  # `with` desugars to nested `case`s; the `else` clause makes it total.
  @spec first_two([a]) :: {:ok, a, a} | :error when a: var
  def first_two(list) do
    with [x | rest] <- list,
         [y | _] <- rest do
      {:ok, x, y}
    else
      _ -> :error
    end
  end

  # String interpolation desugars to a binary built from its parts.
  @spec greet(String.t()) :: String.t()
  def greet(name), do: "Hello, #{name}!"

  # Default arguments: Elixir generates `scale/1` (which calls `scale/2` with the
  # default value) and gives it NO spec of its own. etylizer's BEAM reader
  # *synthesizes* `scale/1`'s spec by dropping the defaulted parameter from
  # `scale/2`'s spec, so both arities check.
  @spec scale([integer()], integer()) :: [integer()]
  def scale(xs, factor \\ 2), do: :lists.map(fn x -> x * factor end, xs)
end
