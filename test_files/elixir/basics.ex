defmodule Basics do
  @spec inc(integer()) :: integer()
  def inc(x), do: x + 1

  @spec inc_fail(integer()) :: atom()
  def inc_fail(x), do: x + 1
end
