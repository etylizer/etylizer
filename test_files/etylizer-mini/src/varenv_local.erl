-module(varenv_local).

% @doc An environment for local variables that might be shadowed.

-export([empty/0,
         insert/2,
         insert_fresh/1,
         lookup/3,
         find/2,
         merge_envs/1
        ]).

-export_type([
    t/0
]).

-opaque t() :: {integer(), #{ atom() => ast:unique_tok() }}.

-include("log.hrl").

% Constructs a new, empty varenv.
-spec empty() -> t().
empty() -> {0, #{}}.

% Inserts a new binding, shadowing an existing binding.
-spec insert(atom(), t()) -> {ast:local_varname(), t()}.
insert(Name, {Next, Map}) ->
    Unique =
        case maps:find(Name, Map) of
            {ok, X} -> X + 1;
            error -> 0
        end,
    {{Name, Unique}, {Next, Map#{ Name => Unique}}}.

% Inserts a binding for a comletely fresh variable
-spec insert_fresh(t()) -> {ast:local_varname(), t()}.
insert_fresh({Next, Map}) ->
    Name = list_to_atom("$X_" ++ integer_to_list(Next)),
    insert(Name, {Next+1, Map}).

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
find(Name, {_, Map}) ->
    case maps:find(Name, Map) of
        {ok, X} -> {ok, {Name, X}};
        error -> error
    end.

% Merge the given local variable environments. Only variables bound in all varenvs are kept.
% (Variables bound in only a subset of the varenvs are considered 'unsafe' in Erlang.)
% All variables kept must have the same unique name. It's a bug if this is not the case.
% The list of varenvs must not be empty
-spec merge_envs([t()]) -> t().
merge_envs([]) -> errors:bug("merge_envs called with empty list");
merge_envs([Init | Rest]) ->
    Combiner =
        fun (K, V1, V2) ->
                if V1 == V2 -> V1;
                   true -> errors:bug("~w is associated with ~w and ~w when merging envs",
                                      [K, V1, V2])
                end
        end,
    lists:foldl(
        fun ({Next1, M}, {Next2, AccMap}) ->
            {max(Next1, Next2), maps:intersect_with(Combiner, M, AccMap)}
        end, Init, Rest).
