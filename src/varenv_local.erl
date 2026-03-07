-module(varenv_local).

% @doc An environment for local variables that might be shadowed.

-export([empty/0, empty/1,
         insert/2,
         insert_fresh/1,
         lookup/3,
         find/2,
         find_ref/2,
         merge_envs/1,
         merge/2,
         new_bindings/2,
         mark_escaped/2
        ]).

-export_type([
    t/0
]).

-opaque t() :: {integer(), #{ atom() => ast:unique_tok() }, #{ atom() => integer()}, sets:set(ast:local_varname()) }.

-include("log.hrl").

% Constructs a new, empty varenv.
-spec empty() -> t().
empty() -> {0, #{}, #{}, sets:new()}.

% new environment with remembering where to start counting
-spec empty(t()) -> t().
empty({_, M, _, _}) ->
    {0, #{}, maps:map(fun(_K, V) -> V + 1 end, M), sets:new()}.


% Inserts a new binding, shadowing an existing binding.
-spec insert(atom(), t()) -> {ast:local_varname(), t()}.
insert(Name, {Next, Map, Remember, Escaped}) ->
    Unique =
        case maps:find(Name, Map) of
            {ok, X} -> X + 1;
            error -> maps:get(Name, Remember, 0)
        end,
    {{Name, Unique}, {Next, Map#{ Name => Unique}, Remember, Escaped}}.

% Inserts a binding for a comletely fresh variable
-spec insert_fresh(t()) -> {ast:local_varname(), t()}.
insert_fresh({Next, Map, R, Esc}) ->
    Name = list_to_atom("$X_" ++ integer_to_list(Next)),
    insert(Name, {Next+1, Map, R, Esc}).

% Looks up a variable, undefined variables cause an error.
-spec lookup(ast:loc(), atom(), t()) -> ast:local_varname().
lookup(Loc, Name, Env) ->
    case find(Name, Env) of
        error ->
            ?LOG_NOTE("Undefind local variable ~w at ~s, Env=~w",
                      Name, ast:format_loc(Loc), Env),
            errors:name_error(Loc, "Undefined local variable ~w", Name);
        {ok, X} -> X
    end.

% Looks up a variable or return error
-spec find(atom(), t()) -> t:opt(ast:local_varname()).
find(Name, {_, Map, _, _}) ->
    case maps:find(Name, Map) of
        {ok, X} -> {ok, {Name, X}};
        error -> error
    end.

% Looks up a variable and returns the appropriate ref (local_ref or escaped_ref).
-spec find_ref(atom(), t()) -> t:opt(ast:local_ref() | ast:escaped_ref()).
find_ref(Name, {_, Map, _, Escaped}) ->
    case maps:find(Name, Map) of
        {ok, X} ->
            VarName = {Name, X},
            case sets:is_element(VarName, Escaped) of
                true -> {ok, {escaped_ref, VarName, ast:escape_tyvar_name(VarName)}};
                false -> {ok, {local_ref, VarName}}
            end;
        error -> error
    end.

% Merge the given local variable environments. Only variables bound in all varenvs are kept.
% (Variables bound in only a subset of the varenvs are considered 'unsafe' in Erlang.)
% All variables kept must have the same unique name. It's a bug if this is not the case.
% The list of varenvs must not be empty
-spec merge_envs([t()]) -> t().
merge_envs([Init | Rest]) ->
    Combiner =
        fun (K, V1, V2) ->
                if V1 == V2 -> V1;
                   true -> errors:bug("~w is associated with ~w and ~w when merging envs",
                                      [K, V1, V2])
                end
        end,
    lists:foldl(
        fun ({Next1, M, R, Esc1}, {Next2, AccMap, R2, Esc2}) ->
            R = R2, % TODO
            {max(Next1, Next2), maps:intersect_with(Combiner, M, AccMap), R2,
             sets:union(Esc1, Esc2)}
        end, Init, Rest).


-spec merge(t(), t()) -> t().
merge({N1, M1, R1, Esc1}, {N2, M2, R2, Esc2}) ->
  {max(N1, N2), maps:merge(M1, M2), maps:merge(R1, R2), sets:union(Esc1, Esc2)}.

% Returns variables in New that are not in Old (newly introduced bindings).
% The result is sorted so that escape annotations are deterministic
% (caching and test output depend on stable ordering).
-spec new_bindings(Old::t(), New::t()) -> [ast:local_varname()].
new_bindings({_, OldMap, _, _}, {_, NewMap, _, _}) ->
    lists:sort(maps:fold(fun(Name, Tok, Acc) ->
        case maps:find(Name, OldMap) of
            {ok, Tok} -> Acc; % same binding, not new
            _ -> [{Name, Tok} | Acc]
        end
    end, [], NewMap)).

% Mark the given variable names as escaped in the environment.
-spec mark_escaped([ast:local_varname()], t()) -> t().
mark_escaped(VarNames, {N, M, R, Escaped}) ->
    NewEscaped = sets:union(Escaped, sets:from_list(VarNames)),
    {N, M, R, NewEscaped}.
