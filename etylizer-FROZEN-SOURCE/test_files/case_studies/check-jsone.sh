#!/bin/bash
set -e

cd $(dirname $0)

# type errors (true)
# 5) imprecise (transitive) type spec
#
# type errors
# 2) arithmetic on type level
# 4) invariant of non-empty list difficult to express in type specs
# 6) exhaustiveness
# 7) timeout
# 9) type spec
# 10) approximate numbers
# ?) unknown

QF=""
QF=$QF" -i decode/2" # 6)
QF=$QF" -i encode/2" # 6)
QF=$QF" -i term_to_json_string/1" # 2)
../../ety --no-deps -f $QF jsone/src/jsone.erl

QF=""
QF=$QF" -i ip_address_to_json_string" # ?)
QF=$QF" -i format_ipv6/1" # 5) string:lowercase 
QF=$QF" -i to_hex/1" # ?)
../../ety --no-deps -f $QF jsone/src/jsone_inet.erl

QF=""
QF=$QF" -i value/4" # 7)
QF=$QF" -i datetime/4" # 7)
QF=$QF" -i padding/2" # 7)
QF=$QF" -i parse_option/2" # 7)
QF=$QF" -i encode/2" # 9)
QF=$QF" -i string/4" # 9)
QF=$QF" -i format2digit/1" # 7)
QF=$QF" -i format_seconds/1" # 9)
QF=$QF" -i object_key/4" # ?)
QF=$QF" -i escape_string/4" # ?)
QF=$QF" -i unescaped_string_length/3" # ?)
QF=$QF" -i hex/1" # ?)
QF=$QF" -i parse_options/1" # ?)
QF=$QF" -i local_offset/0" # 10)
QF=$QF" -i local_offset_dst/0" # 10)
QF=$QF" -i my_integer_to_list/1" # overlay
QF=$QF" -i format_tz_/1" # ?)
QF=$QF" -i object_members/4" # ?)
QF=$QF" -i next/3" # ?)
../../ety --no-deps -f $QF jsone/src/jsone_encode.erl

# Added 1 type spec
QF=""
QF=$QF" -i string/6" # 7)
QF=$QF" -i parse_option/2" # 7)
QF=$QF" -i object_key" # ?)
QF=$QF" -i next/5" # ?)
QF=$QF" -i number/4" # ?)
QF=$QF" -i number_exponation_part/6" # ?)
../../ety --no-deps -f $QF jsone/src/jsone_decode.erl

#../../ety --build --report-mode report --report-timeout 3000 --type-overlay overlay.erl --no-deps -f -l error -P jsone -S jsone/src
