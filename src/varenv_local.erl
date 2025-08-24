-module(varenv_local).

% @doc An environment for local variables that might be shadowed.

-export([empty/0, empty/1,
         insert/2,
         insert_fresh/1,
         lookup/3,
         find/2,
         merge_envs/1,
         merge/2
        ]).

-export_type([
    t/0
]).

-opaque t() :: {integer(), #{ atom() => ast:unique_tok() }, #{ atom() => integer()} }.

-include("log.hrl").

% Constructs a new, empty varenv.
-spec empty() -> t().
empty() -> {0, #{}, #{}}.

% new environment with remembering where to start counting
-spec empty(t()) -> t().
empty({_, M, _}) ->
    {0, #{}, maps:map(fun(_K, V) -> V + 1 end, M)}.


% Inserts a new binding, shadowing an existing binding.
-spec insert(atom(), t()) -> {ast:local_varname(), t()}.
insert(Name, {Next, Map, Remember}) ->
    Unique =
        case maps:find(Name, Map) of
            {ok, X} -> X + 1;
            error -> maps:get(Name, Remember, 0)
        end,
    {{Name, Unique}, {Next, Map#{ Name => Unique}, Remember}}.

% Inserts a binding for a comletely fresh variable
-spec insert_fresh(t()) -> {ast:local_varname(), t()}.
insert_fresh({Next, Map, R}) ->
    Name = list_to_atom("$X_" ++ integer_to_list(Next)),
    insert(Name, {Next+1, Map, R}).

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
find(Name, {_, Map, _}) ->
    case maps:find(Name, Map) of
        {ok, X} -> {ok, {Name, X}};
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
        fun ({Next1, M, R}, {Next2, AccMap, R2}) ->
            R = R2, % TODO
            {max(Next1, Next2), maps:intersect_with(Combiner, M, AccMap), R2}
        end, Init, Rest).


-spec merge(t(), t()) -> t().
merge({N1, M1, R1}, {N2, M2, R2}) ->
  {max(N1, N2), maps:merge(M1, M2), maps:merge(R1, R2)}.
