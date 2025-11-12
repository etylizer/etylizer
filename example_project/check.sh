#!/bin/bash

cd ety_example && rebar3 compile && cd ..
../ety --build --exhaustiveness-mode disabled --report-timeout 2000 --report-mode report -f -P ety_example -S ety_example/src
../ety --build --exhaustiveness-mode enabled --report-timeout 2000 --report-mode report -f -P ety_example -S ety_example/src

