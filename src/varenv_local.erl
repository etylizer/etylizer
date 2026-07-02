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
         mark_escaped/2,
         escaped_tyvar/2,
         fresh_esc_tyvar/2
        ]).

-export_type([
    t/0
]).

% The components are:
% - the counter for generating fresh variables ($X_...)
% - the bindings (variable name to unique token)
% - the map remembering where to start counting unique tokens in a new scope
% - the escaped variables, mapping each variable to its current escape type
%   variable (assigned per construct occurrence, see ast:escape_annotation())
% - a mutable counter shared by all envs derived from the same root env,
%   used to mint unique escape type variable names per occurrence
-opaque t() :: {integer(),
                #{ atom() => ast:unique_tok() },
                #{ atom() => integer()},
                #{ ast:local_varname() => ast:ty_varname() },
                counters:counters_ref()}.

-include("log.hrl").

% Constructs a new, empty varenv.
-spec empty() -> t().
empty() -> {0, #{}, #{}, #{}, counters:new(1, [])}.

% new environment with remembering where to start counting
-spec empty(t()) -> t().
empty({_, M, _, _, C}) ->
    {0, #{}, maps:map(fun(_K, V) -> V + 1 end, M), #{}, C}.


% Inserts a new binding, shadowing an existing binding.
-spec insert(atom(), t()) -> {ast:local_varname(), t()}.
insert(Name, {Next, Map, Remember, Escaped, C}) ->
    Unique =
        case maps:find(Name, Map) of
            {ok, X} -> X + 1;
            error -> maps:get(Name, Remember, 0)
        end,
    {{Name, Unique}, {Next, Map#{ Name => Unique}, Remember, Escaped, C}}.

% Inserts a binding for a comletely fresh variable
-spec insert_fresh(t()) -> {ast:local_varname(), t()}.
insert_fresh({Next, Map, R, Esc, C}) ->
    Name = list_to_atom("$X_" ++ integer_to_list(Next)),
    insert(Name, {Next+1, Map, R, Esc, C}).

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
find(Name, {_, Map, _, _, _}) ->
    case maps:find(Name, Map) of
        {ok, X} -> {ok, {Name, X}};
        error -> error
    end.

% Looks up a variable and returns the appropriate ref (local_ref or escaped_ref).
-spec find_ref(atom(), t()) -> t:opt(ast:local_ref() | ast:escaped_ref()).
find_ref(Name, {_, Map, _, Escaped, _}) ->
    case maps:find(Name, Map) of
        {ok, X} ->
            VarName = {Name, X},
            case maps:find(VarName, Escaped) of
                {ok, TyVar} -> {ok, {escaped_ref, VarName, TyVar}};
                error -> {ok, {local_ref, VarName}}
            end;
        error -> error
    end.

% Merge the given local variable environments. Only variables bound in all varenvs are kept.
% (Variables bound in only a subset of the varenvs are considered 'unsafe' in Erlang.)
% All variables kept must have the same unique name. It's a bug if this is not the case.
% Escaped variables whose escape type variables differ between the branches are kept with
% an arbitrary (but deterministic) choice; callers must assign a fresh escape type variable
% to every variable newly bound inside the merged branches (see ast:escape_annotation()).
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
        fun ({Next1, M, R, Esc1, C}, {Next2, AccMap, R2, Esc2, _}) ->
            R = R2, % TODO
            {max(Next1, Next2), maps:intersect_with(Combiner, M, AccMap), R2,
             maps:merge_with(fun(_K, V1, V2) -> min(V1, V2) end, Esc1, Esc2), C}
        end, Init, Rest).


-spec merge(t(), t()) -> t().
merge({N1, M1, R1, Esc1, C}, {N2, M2, R2, Esc2, _}) ->
  {max(N1, N2), maps:merge(M1, M2), maps:merge(R1, R2), maps:merge(Esc1, Esc2), C}.

% Returns variables in New that are not in Old (newly introduced bindings).
% The result is sorted so that escape annotations are deterministic
% (caching and test output depend on stable ordering).
-spec new_bindings(Old::t(), New::t()) -> [ast:local_varname()].
new_bindings({_, OldMap, _, _, _}, {_, NewMap, _, _, _}) ->
    lists:sort(maps:fold(fun(Name, Tok, Acc) ->
        case maps:find(Name, OldMap) of
            {ok, Tok} -> Acc; % same binding, not new
            _ -> [{Name, Tok} | Acc]
        end
    end, [], NewMap)).

% Mark the given variables as escaped with the given escape type variables,
% overwriting escape type variables from nested constructs.
-spec mark_escaped([{ast:local_varname(), ast:ty_varname()}], t()) -> t().
mark_escaped(Pairs, {N, M, R, Escaped, C}) ->
    NewEscaped = maps:merge(Escaped, maps:from_list(Pairs)),
    {N, M, R, NewEscaped, C}.

% Returns the escape type variable of an escaped variable.
-spec escaped_tyvar(ast:local_varname(), t()) -> t:opt(ast:ty_varname()).
escaped_tyvar(VarName, {_, _, _, Escaped, _}) ->
    maps:find(VarName, Escaped).

% Mints a fresh escape type variable for the given variable. The name contains
% a counter unique for all envs derived from the same root env, so that each
% binding occurrence of a variable gets its own escape type variable.
-spec fresh_esc_tyvar(ast:local_varname(), t()) -> ast:ty_varname().
fresh_esc_tyvar({Name, Tok}, {_, _, _, _, C}) ->
    I = counters:get(C, 1),
    counters:add(C, 1, 1),
    list_to_atom("$esc_" ++ atom_to_list(Name) ++ "_" ++ integer_to_list(Tok)
                 ++ "_" ++ integer_to_list(I)).
