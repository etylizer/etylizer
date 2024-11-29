#!/bin/bash

cd $(dirname $0)

# range excluded because it's slow, see #161
# ../../ety --build --force --level debug -P . -I src --no-deps --ignore range/1 src/varenv.erl

# merge_envs excluded because it's slow, see #161
# ../../ety --build --force --level debug -P . -I src --no-deps --ignore merge_envs/1 src/varenv_local.erl

# mingle/5, is_same_file/2, unconsult/2, string_ends_with/2, file_exists/1 ignored because of #179
# map_opt/3 ignored because it's not type correct
# quit/3 and quit/2 and sformat_raw/2 and diff_terms/3 and mkdirs/1 and hash_sha1/1 and hash_file/1 require support for binary
# sformat/2 and file_get_lines/1 and timeout/2 require support for try
# everywhere/2 and everything/2 because they are very hard to type check
# with_index/2 ignored because of #181 (spec in OTP is wrong)
# assocs_find/2 because of wrong type spec for lists:keyfind #181
# assocs_find_index/2 because recursive functions are slow to type check
# ../../ety --build --force --level debug -P . -I src --no-deps --ignore mingle/5 --ignore is_same_file/2 --ignore map_opt/3 --ignore quit/3 --ignore quit/2 --ignore sformat_raw/2 --ignore sformat/2 --ignore everything/2 --ignore everywhere/2 --ignore diff_terms/3 --ignore file_get_lines/1 --ignore unconsult/2 --ignore string_ends_with/2 --ignore with_index/2 --ignore mkdirs/1 --ignore hash_sha1/1 --ignore hash_file/1 --ignore assocs_find/2 --ignore assocs_find_index/2 --ignore timeout/2 --ignore file_exists/1 src/utils.erl

# tmp_dir/0 because of nonempty_string bug #183
# NOT FINISHED
# ../../ety --build --force --level debug -P . -I src --no-deps --ignore tmp_dir/0 src/tmp.erl

# ../../ety --build --force --level debug -P . -I src --no-deps src/t.erl
# ../../ety --build --force --level debug -P . -I src --no-deps src/errors.erl

# NOT FINISHED: too slow because of inference
# ../../ety --build --force --level debug -P . -I src --no-deps src/stdtypes.erl

# Does not work because of #182
# ../../ety --build --force --level debug -P . -I src --no-deps src/ast_transform.erl

# Does not work because of #179
# ../../ety --build --force --level debug -P . -I src --no-deps src/ast.erl
#
# FULL
# ../../ety --build --force --level debug -P . -I src "$@"
