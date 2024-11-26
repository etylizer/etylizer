#!/bin/bash

cd $(dirname $0)

# range excluded because it's slow, see #161
# ../../ety --build --force --level debug -P . -I src --no-deps --ignore range/1 src/varenv.erl

# merge_envs excluded because it's slow, see #161
# ../../ety --build --force --level debug -P . -I src --no-deps --ignore merge_envs/1 src/varenv_local.erl

# mingle/5, list_uniq_1/2, lists_enumerate_1/2, is_same_file/2, unconsult/2, string_ends_with/2 ignored because of #179
# map_opt/3 ignored because it's not type correct
# quit/3 and quit/2 and sformat_raw/2 and diff_terms/3 require support for binary
# sformat/2 and file_get_lines/1 require support for try
# everywhere/2 and everything/2 because they are very hard to type check
../../ety --build --force --level debug -P . -I src --no-deps --ignore mingle/5 --ignore list_uniq_1/2 --ignore lists_enumerate_1/2 --ignore is_same_file/2 --ignore map_opt/3 --ignore quit/3 --ignore quit/2 --ignore sformat_raw/2 --ignore sformat/2 --ignore everything/2 --ignore everywhere/2 --ignore diff_terms/3 --ignore file_get_lines/1 --ignore unconsult/2 --ignore string_ends_with/2 src/utils.erl

# FULL
# ../../ety --build --force --level debug -P . -I src "$@"
