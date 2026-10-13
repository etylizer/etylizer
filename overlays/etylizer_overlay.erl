-module(etylizer_overlay).

-compile([export_all, nowarn_export_all]).



% TODO ets:update_counter could be improved with an intersection type
-spec 'ets:update_counter' (reference() | atom(), term(), integer() | {integer(), integer()}) -> integer().
'ets:update_counter'(_, _, _) -> error(badarg).

% TODO stdlib list overlays
-spec 'lists:foldl'(fun((T, Acc) -> Acc), Acc, [T]) -> Acc.
'lists:foldl'(_, _, _) -> error(badarg).
-spec 'lists:foldr'(fun((T, Acc) -> Acc), Acc, [T]) -> Acc.
'lists:foldr'(_, _, _) -> error(badarg).
% The process dictionary holds any terms. The specs of OTP name the value with a type variable
% that nothing bounds from below, which the checker takes to be none().
-spec 'erlang:get'(term()) -> term().
'erlang:get'(_) -> error(overlay).

-spec 'erlang:get'() -> [{term(), term()}].
'erlang:get'() -> error(overlay).

% argparse checks the command and the options at run time, and gives the values of the
% arguments as terms
-spec 'argparse:parse'([string()], map(), map()) -> {ok, #{atom() => term()}, [atom()], map()} | {error, term()}.
'argparse:parse'(_, _, _) -> error(overlay).
-spec 'argparse:help'(map(), map()) -> unicode:chardata().
'argparse:help'(_, _) -> error(overlay).
-spec 'argparse:format_error'(term()) -> unicode:chardata().
'argparse:format_error'(_) -> error(overlay).

-spec 'application:load'(atom()) -> ok | {error, term()}.
'application:load'(_) -> error(overlay).

% the value of a key of an application is any term
-spec 'application:get_key'(atom(), atom()) -> undefined | {ok, term()}.
'application:get_key'(_, _) -> error(overlay).

% encodes any term, a term that has no JSON form is an error at run time
-spec 'json:encode'(term()) -> iodata().
'json:encode'(_) -> error(overlay).

-spec 'maps:intersect_with'(fun((Key, Value, Value) -> Value), #{Key => Value}, #{Key => Value}) -> #{Key => Value}.
'maps:intersect_with'(_, _, _) -> error(overlay).

% with a stacktrace it never returns
-spec 'erlang:raise'(error | exit | throw, term(), erlang:stacktrace()) -> no_return().
'erlang:raise'(_, _, _) -> error(overlay).

% write/1 writes latin1, a character above 255 is escaped: the text is an iolist
-spec 'io_lib:write'(term()) -> iolist().
'io_lib:write'(_) -> error(overlay).

% erl_parse and erl_pp have their own types for the abstract format, ast_erl describes
% the same terms
-spec 'erl_parse:parse_exprs'([erl_scan:token()]) -> {ok, [ast_erl:exp()]} | {error, erl_parse:error_info()}.
'erl_parse:parse_exprs'(_) -> error(overlay).
-spec 'erl_parse:parse_form'([erl_scan:token()]) -> {ok, ast_erl:form()} | {error, erl_parse:error_info()}.
'erl_parse:parse_form'(_) -> error(overlay).
-spec 'erl_parse:map_anno'(fun((ast_erl:anno()) -> ast_erl:anno()), ast_erl:exp()) -> ast_erl:exp();
                          (fun((ast_erl:anno()) -> ast_erl:anno()), ast_erl:pat()) -> ast_erl:pat().
'erl_parse:map_anno'(_, _) -> error(overlay).
-spec 'erl_pp:expr'(ast_erl:exp()) -> io_lib:chars().
'erl_pp:expr'(_) -> error(overlay).
-spec 'erl_pp:form'(ast_erl:form()) -> io_lib:chars().
'erl_pp:form'(_) -> error(overlay).

% in OTP the term is a variable of the spec with the bound term()
-spec 'erl_parse:parse_term'([erl_scan:token()]) -> {ok, term()} | {error, erl_parse:error_info()}.
'erl_parse:parse_term'(_) -> error(overlay).

% evaluates any term, a term that is no expression is an error at run time
-spec 'erl_eval:expr'(term(), map()) -> {value, term(), term()}.
'erl_eval:expr'(_, _) -> error(overlay).

-spec 'lists:mapfoldl'(fun((A, Acc) -> {B, Acc}), Acc, [A]) -> {[B], Acc}.
'lists:mapfoldl'(_, _, _) -> error(badarg).
-spec 'lists:map'
  (fun((A) -> B), nonempty_list(A)) -> nonempty_list(B);
  (fun((A) -> B), list(A)) -> list(B).
'lists:map'(_, _) -> error(badarg).

% more precise filtermap spec needed for ty_map:split_into_associations
% basically a replacement for list comprehensions with filters
-spec 'lists:filtermap'(fun((T) -> boolean()), [T]) -> [T]
                ; (fun((T) -> {true, U} | false), [T]) -> [U]
                ; (fun((T) -> {true, U} | boolean()), [T]) -> [T | U].
'lists:filtermap'(_, _) -> error(badarg).

-spec 'lists:usort'
  (fun((T, T) -> boolean()), nonempty_list(T)) -> nonempty_list(T);
  (fun((T, T) -> boolean()), list(T)) -> list(T).
'lists:usort'(_, _) -> error(overlay).

-spec 'lists:usort'
  (nonempty_list(T)) -> nonempty_list(T);
  (list(T)) -> list(T).
'lists:usort'(_) -> error(overlay).

% the elements are not smaller than the first one
-spec 'lists:seq'
  (pos_integer(), integer()) -> [pos_integer()];
  (non_neg_integer(), integer()) -> [non_neg_integer()];
  (integer(), integer()) -> [integer()].
'lists:seq'(_, _) -> error(overlay).

% counts from 1
-spec 'lists:enumerate'([T]) -> [{pos_integer(), T}].
'lists:enumerate'(_) -> error(overlay).

-spec 'lists:unzip'
  (nonempty_list({A, B})) -> {nonempty_list(A), nonempty_list(B)};
  (list({A, B})) -> {list(A), list(B)}.
'lists:unzip'(_) -> error(overlay).

-spec 'lists:unzip3'
  (nonempty_list({A, B, C})) -> {nonempty_list(A), nonempty_list(B), nonempty_list(C)};
  (list({A, B, C})) -> {list(A), list(B), list(C)}.
'lists:unzip3'(_) -> error(overlay).

-spec 'lists:keysort'(1, [{K, V}]) -> [{K, V}].
'lists:keysort'(1, _) -> error(overlay).

-spec 'lists:keyfind'(Key, pos_integer(), [{Key, Value}]) -> {Key, Value} | false.
'lists:keyfind'(_, _, _) -> error(overlay).

-spec 'lists:reverse'
  (nonempty_list(T)) -> nonempty_list(T);
  (list(T)) -> list(T).
'lists:reverse'(_) -> error(overlay).


-spec 'erlang:length'
    (list(_)) -> non_neg_integer();
    (nonempty_list(_)) -> pos_integer().
'erlang:length'(_List) -> error(overlay).

-spec 'erlang:tl'(nonempty_list(A)) -> [A].
'erlang:tl'(_List) -> error(overlay).

-spec 'erlang:hd'(nonempty_list(A)) -> A.
'erlang:hd'(_List) -> error(overlay).

-type deepList(A) :: [A | deepList(A)].
-spec 'lists:flatten'(deepList(A)) -> [A].
'lists:flatten'(_) -> error(overlay).

% TODO bdd.hrl:espresso_split_line_into_elements_and_result/1: why is string() not compatible with [chardata()]?
-spec 'string:to_upper'(string()) -> string(); (nonempty_string()) -> nonempty_string().
'string:to_upper'(_) -> error(badarg).
-spec 'string:split'(string(), string()) -> [string()].
'string:split'(_, _) -> error(badarg).
-spec 'string:split'(string(), string(), all) -> [string()].
'string:split'(_, _, _) -> error(badarg).
-spec 'string:slice'(string(), non_neg_integer(), non_neg_integer()) -> string().
'string:slice'(_, _, _) -> error(badarg).
% the pieces of the string, with the replacement between them
-spec 'string:replace'(string(), string(), string(), all | leading | trailing) -> [string()].
'string:replace'(_, _, _, _) -> error(badarg).
-spec 'string:trim'(string()) -> string().
'string:trim'(_) -> error(badarg).
-spec 'string:trim'(string(), leading | trailing | both) -> string().
'string:trim'(_, _) -> error(badarg).
-spec 'string:trim'(string(), leading | trailing | both, [char()]) -> string().
'string:trim'(_, _, _) -> error(badarg).
-spec 'os:cmd'(string()) -> string().
'os:cmd'(_) -> error(badarg).
-spec 'file:write_file'(string(), string() | iodata()) -> _.
'file:write_file'(_, _) -> error(badarg).

-spec 'io:get_line'(pid(), string()) -> string() | eof.
'io:get_line'(_, _) -> error(overlay).

-spec 'maps:get'(Key, #{Key => Value}) -> Value.
'maps:get'(_, _) -> error(badarg).
-spec 'maps:put'(Key, Value, #{Key => Value}) -> #{Key => Value}.
'maps:put'(_, _, _) -> error(badarg).
-spec 'maps:is_key'(Key, #{Key => _Value}) -> boolean().
'maps:is_key'(_, _) -> error(badarg).
-spec 'maps:remove'(Key, #{Key => Value}) -> #{Key => Value}.
'maps:remove'(_, _) -> error(badarg).
-spec 'maps:from_list'([{Key, Value}]) -> #{Key => Value}.
'maps:from_list'(_) -> error(badarg).
-spec 'maps:to_list'(#{Key => Value}) -> list({Key, Value}).
'maps:to_list'(_) -> error(badarg).
-spec 'maps:fold'(fun((Key, Value, Acc) -> Acc), Acc, #{Key => Value}) -> Acc.
'maps:fold'(_, _, _) -> error(badarg).
-spec 'maps:merge'(#{Key => Value}, #{Key => Value}) -> #{Key => Value}.
'maps:merge'(_, _) -> error(badarg).
-spec 'maps:map'(fun((Key, Value1) -> Value2), #{Key => Value1}) -> #{Key => Value2}.
'maps:map'(_, _) -> error(overlay).
-spec 'maps:update_with'(Key, fun((Value) -> Value), Value, #{Key => Value}) -> #{Key => Value}.
'maps:update_with'(_, _, _, _) -> error(overlay).
-spec 'maps:find'(Key, #{Key => Value}) -> {ok, Value} | error.
'maps:find'(_, _) -> error(overlay).
-spec 'maps:get'(Key, #{Key => Value}, Value) -> Value.
'maps:get'(_, _, _) -> error(overlay).
-spec 'maps:keys'(#{Key => _Value}) -> [Key].
'maps:keys'(_) -> error(overlay).
-spec 'maps:values'(#{_Key => Value}) -> [Value].
'maps:values'(_) -> error(overlay).
-spec 'maps:size'(#{_Key => _Value}) -> non_neg_integer().
'maps:size'(_) -> error(overlay).
-spec 'maps:without'([Key], #{Key => Value}) -> #{Key => Value}.
'maps:without'(_, _) -> error(overlay).
-spec 'maps:foreach'(fun((Key, Value) -> _), #{Key => Value}) -> ok.
'maps:foreach'(_, _) -> error(overlay).

% filename overlays
-spec 'filename:join'(string(), string()) -> string().
'filename:join'(_, _) -> error(overlay).
-spec 'filename:join'([string()]) -> string().
'filename:join'(_) -> error(overlay).
-spec 'filename:basename'(string(), string()) -> string().
'filename:basename'(_, _) -> error(overlay).
-spec 'filename:basename'(string()) -> string().
'filename:basename'(_) -> error(overlay).
-spec 'filename:dirname'(string()) -> string().
'filename:dirname'(_) -> error(overlay).
-spec 'filename:basedir'(atom(), string()) -> string().
'filename:basedir'(_, _) -> error(overlay).
-spec 'filename:nativename'(string()) -> string().
'filename:nativename'(_) -> error(overlay).
-spec 'filename:rootname'(string()) -> string().
'filename:rootname'(_) -> error(overlay).
-spec 'filename:extension'(string()) -> string().
'filename:extension'(_) -> error(overlay).

% filelib overlays
-spec 'filelib:ensure_dir'(string()) -> ok | {error, term()}.
'filelib:ensure_dir'(_) -> error(overlay).
-spec 'filelib:is_regular'(string()) -> boolean().
'filelib:is_regular'(_) -> error(overlay).
-spec 'filelib:is_dir'(string()) -> boolean().
'filelib:is_dir'(_) -> error(overlay).
-spec 'filelib:is_file'(string()) -> boolean().
'filelib:is_file'(_) -> error(overlay).

% file overlays
-spec 'file:read_file'(string()) -> {ok, binary()} | {error, term()}.
'file:read_file'(_) -> error(overlay).
-spec 'file:list_dir'(string()) -> {ok, [string()]} | {error, term()}.
'file:list_dir'(_) -> error(overlay).
-spec 'file:open'(string(), [atom()]) -> {ok, pid()} | {error, term()}.
'file:open'(_, _) -> error(overlay).
-spec 'file:copy'(string(), string()) -> {ok, non_neg_integer()} | {error, term()}.
'file:copy'(_, _) -> error(overlay).
-spec 'file:change_mode'(string(), non_neg_integer()) -> ok | {error, term()}.
'file:change_mode'(_, _) -> error(overlay).
-spec 'file:consult'(string()) -> {ok, [term()]} | {error, term()}.
'file:consult'(_) -> error(overlay).
