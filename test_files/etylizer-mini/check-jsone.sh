#!/bin/bash
set -e

cd $(dirname $0)

# crashes
# 1) try-catch
#
# type errors (true)
# 5) imprecise (transitive) type spec
#
# type errors
# 2) arithmetic on type level
# 3) binary patterns too imprecise
# 4) invariant of non-empty list difficult to express in type specs
# 6) exhaustiveness
# 7) timeout
# 8) default records
# 9) type spec
# 10) approximate numbers
# ?) unknown

QF=""
QF=$QF" -i decode/2" # 1)
QF=$QF" -i encode/2" # 1)
QF=$QF" -i term_to_json_string/1" # 2)
QF=$QF" -i check_decode_remainings/1" # 3)
../../ety --no-deps -f $QF -l info jsone/src/jsone.erl

QF=""
QF=$QF" -i ip_address_to_json_string" # ?)
QF=$QF" -i format_ipv6/1" # 5) string:lowercase 
QF=$QF" -i to_hex/1" # ?)
../../ety --no-deps -f $QF -l info jsone/src/jsone_inet.erl

QF=""
QF=$QF" -i value/4" # 1)
QF=$QF" -i datetime/4" # 7)
QF=$QF" -i padding/2" # 7)
QF=$QF" -i parse_option/2" # 7)
QF=$QF" -i encode/2" # 9)
QF=$QF" -i string/4" # 9)
QF=$QF" -i format2digit/1" # 7)
QF=$QF" -i format_seconds/1" # 9)
QF=$QF" -i object_key/4" # ?)
QF=$QF" -i escape_string/4" # 3)
QF=$QF" -i unescaped_string_length/3" # 3)
QF=$QF" -i hex/1" # ?)
QF=$QF" -i parse_options/1" # 8)
QF=$QF" -i local_offset/0" # 10)
QF=$QF" -i local_offset_dst/0" # 10)
QF=$QF" -i my_integer_to_list/1" # overlay
QF=$QF" -i format_tz_/1" # ?)
QF=$QF" -i object_members/4" # ?)
../../ety --no-deps -f $QF -l info jsone/src/jsone_encode.erl

# Added 1 type spec
QF=""
QF=$QF" -i string/6" # 7)
QF=$QF" -i parse_option/2" # 7)
QF=$QF" -i object_key" # 1)
QF=$QF" -i unicode_string" # 1)
QF=$QF" -i number_exponation_part" # 1)
QF=$QF" -i next/5" # 3)
QF=$QF" -i whitespace/5" # 3)
QF=$QF" -i value/4" # 3)
QF=$QF" -i array/4" # 3)
QF=$QF" -i array_next/5" # 3)
QF=$QF" -i object/4" # 3)
QF=$QF" -i object_value/6" # 3)
QF=$QF" -i object_next/5" # 3)
QF=$QF" -i number/4" # 3)
QF=$QF" -i number_integer_parts/5" # 3)
QF=$QF" -i number_integer_part/5" # 3)
QF=$QF" -i number_fraction_part/6" # 3)
QF=$QF" -i number_fraction_part_rest/7" # 8)
QF=$QF" -i parse_options/1" # 8)
../../ety --no-deps -f $QF -l info jsone/src/jsone_decode.erl

../../ety --build --report-mode report --report-timeout 3000 --type-overlay overlay.erl --no-deps -f -l error -P jsone -S jsone/src
