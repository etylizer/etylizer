#!/bin/bash

cd ety_example && rebar3 compile && cd ..
../ety --build --report-timeout 2000 --report-mode report -f -P ety_example -S ety_example/src



