#!/bin/bash

cd ety_example_ex && mix compile && cd ..
../ety --build -a /usr/lib/elixir/lib/elixir/ebin --report-mode report --report-timeout 5000 -f ety_example_ex/_build/dev/lib/ety_example_ex/ebin/Elixir.*.beam
../ety --build -a /usr/lib/elixir/lib/elixir/ebin --type-overlay ../overlays/elixir_overlay.erl --report-mode report --report-timeout 5000 -f ety_example_ex/_build/dev/lib/ety_example_ex/ebin/Elixir.*.beam
