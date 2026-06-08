defmodule EtyExampleEx.MixProject do
  use Mix.Project

  # A minimal Mix project used to demonstrate etylizer on Elixir code.
  # etylizer type checks the *compiled* BEAM output of this project, so the
  # only requirement is that `mix compile` produces debug_info (the default).
  def project do
    [
      app: :ety_example_ex,
      version: "0.1.0",
      elixir: "~> 1.16",
      start_permanent: false,
      deps: deps()
    ]
  end

  def application do
    [extra_applications: [:logger]]
  end

  defp deps do
    []
  end
end
