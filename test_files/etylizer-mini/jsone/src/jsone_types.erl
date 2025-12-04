-module(jsone_types).
% we need a separate module because of bug #268

-export_type([json_value/0,
              json_boolean/0,
              json_number/0,
              json_string/0,
              json_array/0,
              json_object/0,
              json_object_members/0,
              json_term/0,
              json_object_format_tuple/0,
              json_object_format_proplist/0,
              json_object_format_map/0,
              json_scalar/0,

              encode_option/0,
              decode_option/0,
              float_format_option/0,
              datetime_encode_format/0,
              datetime_format/0,
              timezone/0,
              utc_offset_seconds/0,
              stack_item/0]).

%%--------------------------------------------------------------------------------
%% Types & Macros
%%--------------------------------------------------------------------------------
-type json_value() :: json_number() |
                      json_string() |
                      json_array() |
                      json_object() |
                      json_boolean() |
                      null |
                      undefined |
                      json_term().
-type json_boolean() :: boolean().
-type json_number() :: number().
-type json_string() :: binary() | atom() | calendar:datetime().  % NOTE: `decode/1' always returns `binary()' value
-type json_array() :: [json_value()].
-type json_object() :: json_object_format_tuple() | json_object_format_proplist() | json_object_format_map().
-type json_object_members() :: [{json_string(), json_value()}].
-type json_term() :: {{json, iolist()}} | {{json_utf8, unicode:chardata()}}.
%% `json_term()' allows inline already encoded JSON value. `json' variant
%% expects byte encoded utf8 data values as list members. `json_utf8' expect
%% Unicode code points as list members. Binaries are copied "as is" in both
%% variants except `json_utf8' will check if binary contain valid `UTF-8'
%% encoded data. In short, `json' uses `erlang:iolist_to_binary/1' and
%% `json_utf8' uses `unicode:chardata_to_binary/1' for encoding.
%%
%% A simple example is worth a thousand words.
%%
%% ```
%% 1> S = "hélo".
%% "hélo"
%% 2> shell:strings(false).
%% true
%% 3> S.
%% [104,233,108,111]
%% 4> B = jsone:encode({{json, S}}).  % invalid UTF-8
%% <<104,233,108,111>>
%% 5> B2 = jsone:encode({{json_utf8, S}}). % valid UTF-8
%% <<104,195,169,108,111>>
%% 6> jsone:encode({{json, B}}).
%% <<104,233,108,111>>
%% 7> jsone:encode({{json_utf8, B}}).
%% ** exception error: {invalid_json_utf8,<<104>>,<<233,108,111>>}
%%      in function  jsone_encode:value/4
%%         called as jsone_encode:value({json_utf8,<<104,233,108,111>>},
%%                                      [],<<>>,
%%                                      {encode_opt_v2,false,
%%                                                     [{scientific,20}],
%%                                                     {iso8601,0},
%%                                                     string,0,0})
%%      in call from jsone:encode/2 (/home/hynek/work/altworx/jsone/_build/default/lib/jsone/src/jsone.erl, line 302)
%% 8> jsone:encode({{json_utf8, B2}}).
%% <<104,195,169,108,111>>
%% 9> shell:strings(true).
%% false
%% 10> jsone:encode({{json_utf8, B2}}).
%% <<"hélo"/utf8>>
%% 11> jsone:encode({{json, binary_to_list(B2)}}). % UTF-8 encoded list leads to valid UTF-8
%% <<"hélo"/utf8>>
%% '''
%%
-type json_object_format_tuple() :: {json_object_members()}.
-type json_object_format_proplist() :: [{}] | json_object_members().

-ifdef('NO_MAP_TYPE').
-opaque json_object_format_map() :: json_object_format_proplist().
%% `maps' is not supported in this erts version
-else.
-type json_object_format_map() :: map().
-endif.

-type json_scalar() :: json_boolean() | json_number() | json_string().

-type float_format_option() :: {scientific, Decimals :: 0..249} | {decimals, Decimals :: 0..253} | compact | short.
%% `scientific': <br />
%% - The float will be formatted using scientific notation with `Decimals' digits of precision. <br />
%%
%% `decimals': <br />
%% - The encoded string will contain at most `Decimals' number of digits past the decimal point. <br />
%% - If `compact' is provided the trailing zeros at the end of the string are truncated. <br />
%% - If `short' is provided the float is formatted with the smallest number of digits. <br />
%%
%% For more details, see <a href="http://erlang.org/doc/man/erlang.html#float_to_list-2">erlang:float_to_list/2</a>.
%%
%% ```
%% > jsone:encode(1.23).
%% <<"1.22999999999999998224e+00">>
%%
%% > jsone:encode(1.23, [{float_format, [{scientific, 4}]}]).
%% <"1.2300e+00">>
%%
%% > jsone:encode(1.23, [{float_format, [{scientific, 1}]}]).
%% <<"1.2e+00">>
%%
%% > jsone:encode(1.23, [{float_format, [{decimals, 4}]}]).
%% <<"1.2300">>
%%
%% > jsone:encode(1.23, [{float_format, [{decimals, 4}, compact]}]).
%% <<"1.23">>
%% '''

-type datetime_encode_format() :: Format :: datetime_format() | {Format :: datetime_format(), TimeZone :: timezone()}.
%% Datetime encoding format.
%%
%% The default value of `TimeZone' is `utc'.
%%
%% ```
%% %
%% % Universal Time
%% %
%% > jsone:encode({{2000, 3, 10}, {10, 3, 58}}, [{datetime_format, iso8601}]).
%% <<"\"2000-03-10T10:03:58Z\"">>
%%
%% %
%% % Local Time (JST)
%% %
%% > jsone:encode({{2000, 3, 10}, {10, 3, 58}}, [{datetime_format, {iso8601, local}}]).
%% <<"\"2000-03-10T10:03:58+09:00\"">>
%%
%% % Also you can use {iso8601, local_dst} to properly calculate the timezone according to the daylight saving procedure. Consider using it, if the executing computer is located in a country that implements this procedure
%%
%% %
%% % Explicit TimeZone Offset
%% %
%% > jsone:encode({{2000, 3, 10}, {10, 3, 58}}, [{datetime_format, {iso8601, -2*60*60}}]).
%% <<"\"2000-03-10T10:03:58-02:00\"">>
%% '''

-type datetime_format() :: iso8601.
-type timezone() :: utc | local | local_dst | utc_offset_seconds().
-type utc_offset_seconds() :: -86399..86399.

-type common_option() :: undefined_as_null.
%%
%% `undefined_as_null': <br />
%% - Treats `undefined' in Erlang as the conversion target for `null' in JSON. This means that `undefined' will be encoded to `null' and `null' will be decoded to `undefined'<br />

-type encode_option() :: native_utf8 |
                         native_forward_slash |
                         canonical_form |
                         {float_format, [float_format_option()]} |
                         {datetime_format, datetime_encode_format()} |
                         {object_key_type, string | scalar | value} |
                         {space, non_neg_integer()} |
                         {indent, non_neg_integer()} |
                         {map_unknown_value, undefined | fun((term()) -> {ok, json_value()} | error)} |
                         skip_undefined |
                         common_option().
%% `native_utf8': <br />
%% - Encodes non ASCII UTF-8 characters as a human-readable(non-escaped) string <br />
%%
%% `native_forward_slash': <br />
%% - Prevents forward slashes in a JSON string from being escaped <br />
%%
%% `canonical_form': <br />
%% - produce a canonical form of a JSON document <br />
%%
%% `{float_format, Options}':
%% - Encodes a `float()` value in the format which specified by `Options' <br />
%% - default: `[{scientific, 20}]' <br />
%%
%% `{datetime_format, Format}`:
%% - Encodes a `calendar:datetime()` value in the format which specified by `Format' <br />
%% - default: `{iso8601, utc}' <br />
%%
%% `object_key_type':
%% - Allowable object key type <br />
%% - `string': Only string values are allowed (i.e. `json_string()' type) <br />
%% - `scalar': In addition to `string', following values are allowed: nulls, booleans, numerics (i.e. `json_scalar()' type) <br />
%% - `value': Any json compatible values are allowed (i.e. `json_value()' type) <br />
%% - default: `string' <br />
%% - NOTE: If `scalar' or `value' option is specified, non `json_string()' key will be automatically converted to a `binary()' value (e.g. `1' => `<<"1">>', `#{}' => `<<"{}">>') <br />
%%
%% `{space, N}': <br />
%% - Inserts `N' spaces after every comma and colon <br />
%% - default: `0' <br />
%%
%% `{indent, N}': <br />
%% - Inserts a newline and `N' spaces for each level of indentation <br />
%% - default: `0' <br />
%%
%% `skip_undefined': <br />
%% - If specified, each entry having `undefined' value in a object isn't included in the result JSON <br />
%%
%% `{map_unknown_value, Fun}`: <br />
%% - If `Fun' is a function, unknown values encountered during an encoding process are converted to `json_value()` by applying `Fun'. <br />
%% - If `Fun' is `undefined', the encoding results in an error if there are unknown values. <br />
%% - default: `term_to_json_string/1' <br />

-type decode_option() :: {object_format, tuple | proplist | map} |
                         {allow_ctrl_chars, boolean()} |
                         reject_invalid_utf8 |
                         {'keys', 'binary' | 'atom' | 'existing_atom' | 'attempt_atom'} |
                         {duplicate_map_keys, first | last} |
                         common_option().
%% `object_format': <br />
%% - Decoded JSON object format <br />
%% - `tuple': An object is decoded as `{[]}' if it is empty, otherwise `{[{Key, Value}]}'. <br />
%% - `proplist': An object is decoded as `[{}]' if it is empty, otherwise `[{Key, Value}]'. <br />
%% - `map': An object is decoded as `#{}' if it is empty, otherwise `#{Key => Value}'. <br />
%% - default: `map' if OTP version is OTP-17 or more, `tuple' otherwise <br />
%%
%% `allow_ctrl_chars': <br />
%% - If the value is `true', strings which contain unescaped control characters will be regarded as a legal JSON string <br />
%% - default: `false'<br />
%%
%% `reject_invalid_utf8': <br />
%% - Rejects JSON strings which contain invalid UTF-8 byte sequences <br />
%%
%% `keys': <br />
%% Defines way how object keys are decoded. The default value is `binary'.
%% The option is compatible with `labels' option in `jsx'. <br />
%% - `binary': The key is left as a string which is encoded as binary. It's default
%% and backward compatible behaviour. <br />
%% - `atom': The key is converted to an atom. Results in `badarg' if Key value
%% regarded as UTF-8 is not a valid atom. <br />
%% - `existing_atom': Returns existing atom. Any key value which is not
%% existing atom raises `badarg' exception. <br />
%% - `attempt_atom': Returns existing atom as `existing_atom' but returns a
%% binary string if fails find one.
%%
%% `duplicate_map_keys': <br />
%% https://www.ietf.org/rfc/rfc4627.txt says that keys SHOULD be
%% unique, but they don't have to be. Most JSON parsers will either
%% give you the value of the first, or last duplicate property
%% encountered. When `object_format' is `tuple' or `proplist' all
%% duplicates are returned. When `object_format' is `map' by default
%% the first instance of a duplicate is returned. Setting
%% `duplicate_map_keys' to `last' will change this behaviour to return
%% the last such instance.
%% - If the value is `first' then the first duplicate key/value is returned.  <br />
%% - If the value is `last' then the last duplicate key/value is returned.
%% - default: `first'<br />
%%

-type stack_item() :: {Module :: module(),
                       Function :: atom(),
                       Arity :: arity() | (Args :: [term()]),
                       Location :: [{file, Filename :: string()} | {line, Line :: pos_integer()}]}.
%% An item in a stack back-trace.
%%
%% Note that the `erlang' module already defines the same `stack_item/0' type,
%% but it is not exported from the module.
%% So, maybe as a temporary measure, we redefine this type for passing full dialyzer analysis.
