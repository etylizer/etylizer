-module(ast_check).

% @doc This module checks that the parse tree of some file is covered ty the type
% specs in the ast module. We do this check to make sure our definitions in ast
% are correct. See function check/3.

-include_lib("log.hrl").
-include_lib("parse.hrl").
-include_lib("eunit/include/eunit.hrl").

-export([
         check/3,
         check/4,
         check_against_type/4,
         prepare_spec/2,
         parse_spec/1,
         merge_specs/1
        ]).
-export_type([ty_map/0]).

% The first argument is the ty_map obtain from the ast module.
% The second argument is a filename.
% The function checks that parsing the file yields a list of forms that match
% the types in the ast module.
-spec check(ty_map(), module_name(), string()) -> boolean().
check(Spec, ModuleName, Path) -> check(Spec, ModuleName, Path, #parse_opts{}).

-spec check(ty_map(), module_name(), string(), parse_opts()) -> boolean().
check(Spec, Module, Path, ParseOpts) ->
    ?LOG_NOTE("Checking whether AST for ~s conforms to our assumed specification", Path),
    case parse:parse_file(Path, ParseOpts) of
        {ok, Forms} ->
            check_against_type(Spec, Module, forms, Forms);
        error ->
            ?LOG_ERROR("Could not check AST in ~s because the file could not be parsed", Path),
            false
    end.

-type module_name() :: atom().
-type ty_map_key() :: {module_name(), atom(), arity()}. % qualified
-opaque ty_map() :: #{ty_map_key() => {[atom()], ast_erl:ty()}}.

-spec prepare_spec(module_name(), term()) -> ty_map().
prepare_spec(Module, Forms) ->
    Insert = fun (Form, M) ->
        case Form of
            {attribute, _, type, {Name, Ty, Args}} ->
                maps:put({Module, Name, length(Args)},
                         {lists:map(fun(X) -> ast_erl:ty_varname(X) end, Args), Ty}, M);
            _ -> M
        end
    end,
    lists:foldl(Insert, maps:new(), Forms).

-spec parse_spec(file:filename()) -> {ty_map(), module_name()}.
parse_spec(Path) ->
    Module = list_to_atom(filename:basename(Path, ".erl")),
    SpecForms = parse:parse_file_or_die(Path),
    {prepare_spec(Module, SpecForms), Module}.

-spec merge_specs([ty_map()]) -> ty_map().
merge_specs(Specs) -> lists:foldl(fun maps:merge/2, #{}, Specs).

-spec lookup_ty_or_die(ty_map(), atom(), atom(), [ast_erl:ty()]) -> ast_erl:ty().
lookup_ty_or_die(Spec, Mod, Name, Args) ->
    case lookup_ty(Spec, Mod, Name, Args) of
        error -> ?ABORT("Type ~p:~p/~w not found. Avaible types:~n~200p",
                        Mod, Name, length(Args), maps:keys(Spec));
        {ok, Res} -> Res
    end.

-spec lookup_ty(ty_map(), atom(), atom(), [ast_erl:ty()]) -> error | {ok, ast_erl:ty()}.
lookup_ty(Spec, Mod, Name, Args) ->
    Key = {Mod, Name, length(Args)},
    case maps:find(Key, Spec) of
        error -> error;
        {ok, {Vars, Ty}} -> {ok, inst_ty(Vars, Args, Ty)}
    end.

-spec inst_ty([atom()], [ast_erl:ty()], ast_erl:ty()) -> ast_erl:ty().
inst_ty(Vars, Args, Ty) ->
    NArgs = length(Args),
    NVars = length(Vars),
    if
        NArgs /= NVars ->
            ?ABORT("Arity mismatch when applying ~b arguments to type expecting ~b arguments.~n"
                   "Type: ~p~nArgs: ~p", NArgs, NVars, Ty, Args);
        true ->
            M = maps:from_list(lists:zip(Vars, Args)),
            Replace = fun(T) ->
                case T of
                    {var, _, Name} -> maps:find(Name, M);
                    _ -> error
                end
            end,
            ?LOG_TRACE("Instantiating type ~p with arguments ~p", Ty, Args),
            utils:everywhere(Replace, Ty)
    end.

-spec check_against_type(ty_map(), module_name(), ast_erl:ty() | atom(), term()) -> boolean().
check_against_type(Spec, Module, TyOrTyName, Term) ->
    ResolvedTy =
        if is_atom(TyOrTyName) ->
                case lookup_ty(Spec, Module, TyOrTyName, []) of
                    error -> ?ABORT("Cannot resolve type ~w", TyOrTyName);
                    {ok, X} -> X
                end;
            true -> TyOrTyName
        end,
    Res = check_ty_with_result(Spec, Module, ResolvedTy, Term, 0),
    case Res of
        ok ->
            ?LOG_TRACE("Valid term wrt type ~w:~w:~n~200p", Module, ResolvedTy, Term),
            true;
        {SubTy, SubTerm, Depth} ->
            ?LOG_WARN("Invalid term wrt type ~w:~w:~n~200p~n~nSubterm does not have type ~200p at depth ~p~n~200p",
                Module, TyOrTyName, Term, SubTy, Depth, SubTerm),
            false
    end.

-spec raise(ast_erl:ty(), term(), integer()) -> no_return().
raise(Ty, Term, Depth) -> throw({ast_check_error, {Ty, Term, Depth}}).

-spec raise_unless(boolean(), ast_erl:ty(), term(), integer()) -> ok.
raise_unless(false, Ty, Term, Depth) ->
    throw({ast_check_error, {Ty, Term, Depth}});
raise_unless(true, _Ty, _Term, _Depth) -> ok.

-spec check_ty_with_result(ty_map(), module_name(), ast_erl:ty(), term(), integer()) ->
    ok | {ast_erl:ty(), term(), integer()}.
check_ty_with_result(Spec, CurModule, Ty, Form, Depth) ->
    try
        check_ty(Spec, CurModule, Ty, Form, Depth),
        ok
    catch
        throw:{ast_check_error, X} -> X
    end.

-spec check_ty(ty_map(), module_name(), ast_erl:ty(), term(), integer()) -> ok.
check_ty(Spec, CurModule, Ty, Form, Depth) ->
    ?LOG_TRACE("Checking term ~1000p~nagainst type ~1000p", Form, Ty),
    % The type has the form as specified in ast_erl
    R = case Ty of
        {ann_type, _, [_, Ty2]} -> check_ty(Spec, CurModule, Ty2, Form, Depth);
        {atom, _, Atom} -> raise_unless(Atom =:= Form, Ty, Form, Depth);
        {integer, _, Int} -> raise_unless(Int =:= Form, Ty, Form, Depth);
        {char, _, Char} -> raise_unless(Char =:= Form, Ty, Form, Depth);
        {type, _, binary, [{integer, _, _I1}, {integer, _, _I2}]} ->
            errors:not_implemented({"Checking of types for bitstrings not implemented", Ty});
        {type, _, nil, []} -> raise_unless(Form =:= [], Ty, Form, Depth);
        {type, _, list, [Ty2]} ->
            raise_unless(is_list(Form), Ty, Form, Depth),
            lists:foreach(fun (X) -> check_ty(Spec, CurModule, Ty2, X, Depth + 1) end, Form),
            ok;
        {type, _, 'fun', _} ->
            utils:error("Cannot check term against function type ~p", Ty);
        {type, _, bounded_fun, [_, _]} ->
            utils:error("Cannot check term against function type ~p", Ty);
        {type, _, range, [{integer, _, _I1}, {integer, _, _I2}]} ->
            errors:not_implemented("Checking of types for integer ranges not implemented: ~p", Ty);
        {type, _, map, any} ->
            raise_unless({} =:= Form, Ty, Form, Depth);
        {type, Anno, map, TyAssocs} ->
                case
                    try maps:to_list(Form)
                    catch {badmap, _} -> false
                    end
                of
                    false -> raise(Ty, Form, Depth);
                    List ->
                        % don't care about required fields
                        KeyTy = {type, Anno, union,
                                 lists:map(fun({type, _, _, [K, _]}) -> K end, TyAssocs)},
                        ValTy = {type, Anno, union,
                                 lists:map(fun({type, _, _, [_, V]}) -> V end, TyAssocs)},
                        KvTy = {type, Anno, tuple, [KeyTy, ValTy]},
                        TotalTy = {type, Anno, list, [KvTy]},
                        check_ty(Spec, CurModule, TotalTy, List, Depth)
                end;
        {op, _, _, _, _} ->
            errors:not_implemented({"Checking of types with binary operators not implemented", Ty});
        {op, _, _, _} ->
            errors:not_implemented({"Checking of types with unary operators not implemented", Ty});
        {type, _, any, []} -> ok;
        {type, _, term, []} -> ok;
        {type, _, none, []} -> raise(Ty, Form, Depth);
        {type, _, no_return, []} -> raise(Ty, Form, Depth);
        {type, _, pid, []} -> raise_unless(is_pid(Form), Ty, Form, Depth);
        {type, _, port, []} -> raise_unless(is_port(Form), Ty, Form, Depth);
        {type, _, reference, []} -> raise_unless(is_reference(Form), Ty, Form, Depth);
        {type, _, float, []} -> raise_unless(is_float(Form), Ty, Form, Depth);
        {type, _, integer, []} -> raise_unless(is_integer(Form), Ty, Form, Depth);
        {type, _, arity, []} ->
            raise_unless(is_integer(Form) andalso Form >= 0 andalso Form < 256, Ty, Form, Depth);
        {type, _, char, []} -> raise_unless(utils:is_char(Form), Ty, Form, Depth);
        {type, _, atom, []} -> raise_unless(is_atom(Form), Ty, Form, Depth);
        {type, _, boolean, []} -> raise_unless(is_boolean(Form), Ty, Form, Depth);
        {type, _, string, []} -> raise_unless(utils:is_string(Form), Ty, Form, Depth);
        {type, _, record, _} ->
            errors:not_implemented({"Checking of types with records not implemented", Ty});
        {remote_type, _, [{atom, _, RemoteMod}, {atom, _, Name}, Args]} ->
                case {RemoteMod, Name, Args} of
                    {sets, set, [Ty2]} ->
                        raise_unless(sets:is_set(Form), Ty, Form, Depth),
                        lists:foreach(fun (X) -> check_ty(Spec, CurModule, Ty2, X, Depth + 1) end,
                                  sets:to_list(Form)),
                        ok;
                    _ ->
                        Ty3 = lookup_ty_or_die(Spec, RemoteMod, Name, Args),
                        check_ty(Spec, RemoteMod, Ty3, Form, Depth)
                end;
        {type, _,tuple, any} ->
            raise_unless(is_tuple(Form), Ty, Form, Depth);
        {type, _, tuple, Tys} ->
            raise_unless(is_tuple(Form), Ty, Form, Depth),
            FormList = tuple_to_list(Form),
            raise_unless(length(Tys) =:= length(FormList), Ty, Form, Depth),
            lists:foreach(fun ({T, F}) -> check_ty(Spec, CurModule, T, F, Depth + 1) end,
                lists:zip(Tys, FormList)),
            ok;
        {var, _, Name} ->
            utils:error("Found free type variable ~p", Name);
        {type, _, union, Tys} ->
            Results =
                lists:map(
                    fun (T) -> check_ty_with_result(Spec, CurModule, T, Form, Depth + 1) end,
                    Tys),
            ?LOG_TRACE("Ty=~200p, Form=~200p, Depth=~w, Results=~200p", Ty, Form, Depth, Results),
            case lists:search(fun (X) -> X =:= ok end, Results) of
                {value, _} -> ok;
                false ->
                    Errors = lists:filter(fun (X) -> X =/= ok end, Results),
                    case lists:sort(fun ({_, _, D1}, {_, _, D2}) -> (D2 =< D1) end, Errors) of
                        [] -> utils:error("empty union ~p", Ty);
                        [Err | _] -> throw({ast_check_error, Err})
                    end
            end;
        {user_type, _, Name, Args} ->
            Ty2 = lookup_ty_or_die(Spec, CurModule, Name, Args),
            check_ty(Spec, CurModule, Ty2, Form, Depth);
        _ -> utils:error("unsupported type: ~p", Ty)
    end,
    R.

% Tests

mk_test_ty(T) ->
    Loc = {1,1},
    {type,
     Loc,
     tuple,
     [{atom,Loc,call},
      {user_type,Loc,anno,[]},
      T,
      {type,
       Loc,
       list,
       [T]}]}.

inst_ty_test() ->
    Loc = {1,1},
    TyArg = {user_type, Loc, guard_test,[]},
    TyVar = {var, Loc, 'T'},
    ?assertEqual(mk_test_ty(TyArg), inst_ty(['T'], [TyArg], mk_test_ty(TyVar))).

lookup_ty_test() ->
    Loc = {1,1},
    TyArg = {user_type, Loc, guard_test,[]},
    TyVar = {var, Loc, 'T'},
    Attr = {attribute,
            Loc,
            type,
            {gen_funcall, mk_test_ty(TyVar), [{var,Loc,'T'}]}},
    M = prepare_spec(ast_erl, [Attr]),
    ?LOG_TRACE("M = ~p", M),
    ?assertEqual(mk_test_ty(TyArg), lookup_ty_or_die(M, ast_erl, 'gen_funcall', [TyArg])).

lookup_ty_realworld_test() ->
    Forms = parse:parse_file_or_die("src/ast_erl.erl"),
    M = prepare_spec(ast_erl, Forms),
    ?LOG_TRACE("Forms = ~p", Forms),
    ?LOG_TRACE("M = ~p", M),
    TyArg = {user_type, {1,1}, guard_test,[]},
    T = lookup_ty_or_die(M, ast_erl, 'gen_funcall', [TyArg]),
    ?assertMatch({type, _, tuple, _}, T).

check_realworld_test() ->
    Forms = parse:parse_file_or_die("src/ast_erl.erl"),
    M = prepare_spec(ast_erl, Forms),
    true = check(M, ast_erl, "test_files/ast_check_test.erl").

check_against(TyName, X) ->
    Forms = parse:parse_file_or_die("src/ast_erl.erl"),
    M = prepare_spec(ast_erl, Forms),
    Ty = lookup_ty_or_die(M, ast_erl, TyName, []),
    true = check_against_type(M, ast_erl, Ty, X).

check_antidote1_test() ->
    Exp0 =
        {'fun',
         {47,19},
         {function,
          {atom,{47,23},riak_core},
          {atom,{47,33},staged_join},
          {integer,{47,45},1}}},
    check_against(exp, Exp0).

check_antidote2_test() ->
    Exp = {match,
           {208,21},
           {var,{208,21},'Msg'},
           {op,
            {209,25},
            '++',
            {var,{208,27},'ConfigPrefix'},
            {op,
             {210,25},
             '++',
             {string,
              {209,28},
              ".throttle tiers must include a tier with "},
             {op,
              {211,25},
              '++',
              {var,
               {210,28},
               'LoadFactorMeasure'},
              {string,{211,28}," 0"}}}}},
    check_against(exp, Exp).

check_riak_test() ->
    Exp = {op,
           {205,19},
           '-',
           {integer,{205,20},1}},
    check_against(pat, Exp).
