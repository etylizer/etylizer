defmodule Showcase do
  @moduledoc """
  Every function in this module type checks. 
  """

  # Union argument + occurrence typing: each guard refines `x`, so etylizer
  # knows the result is exactly `:number | :name`.
  @spec classify(integer() | atom()) :: :number | :name
  def classify(x) when is_integer(x), do: :number
  def classify(x) when is_atom(x), do: :name

  # Intersection (overloaded) type: the body is checked against *both* arrows,
  # `integer() -> integer()` and `atom() -> atom()`.
  @spec bump(integer()) :: integer()
  @spec bump(atom()) :: atom()
  def bump(x) when is_integer(x), do: x + 1
  def bump(x), do: x

  # Parametric polymorphism: the tuple's element types are tracked precisely,
  # so the result is exactly `{b, a}` for any `a`, `b`.
  @spec swap({a, b}) :: {b, a} when a: var, b: var
  def swap({a, b}), do: {b, a}

  # Recursion + occurrence typing over a list.
  @spec all_integers?(list()) :: boolean()
  def all_integers?([]), do: true
  def all_integers?([x | rest]) when is_integer(x), do: all_integers?(rest)
  def all_integers?(_), do: false

  # Distributivity of unions over tuples 
  # etylizer proves: `{:ok | :err, integer() | nil}` is the same type
  # as the four-way union on the right.
  @spec dist({:ok | :err, integer() | nil}) ::
          {:ok, integer()} | {:ok, nil} | {:err, integer()} | {:err, nil}
  def dist(x), do: x
end
