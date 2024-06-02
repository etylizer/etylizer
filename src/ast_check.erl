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

-spec lookup_ty(ty_map(), atom(), atom(), [ast_erl:ty()]) -> ast_erl:ty().
lookup_ty(Spec, Mod, Name, Args) ->
    Key = {Mod, Name, length(Args)},
    case maps:find(Key, Spec) of
        error -> ?ABORT("Type ~p not found. Avaible types:~n~200p",
                        Key, maps:keys(Spec));
        {ok, {Vars, Ty}} -> inst_ty(Vars, Args, Ty)
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

-spec check_against_type(ty_map(), module_name(), atom(), term()) -> boolean().
check_against_type(Spec, Module, TyName, Term) ->
    Ty = lookup_ty(Spec, Module, TyName, []),
    Res = check_ty(Spec, Module, Ty, Term),
    if
        Res -> ?LOG_TRACE("Valid term wrt type ~w:~w:~n~200p", Module, TyName, Term);
        true -> ?LOG_WARN("Invalid term wrt type ~w:~w:~n~200p", Module, TyName, Term)
    end,
    Res.

-spec check_ty(ty_map(), module_name(), ast_erl:ty(), term()) -> boolean().
check_ty(Spec, CurModule, Ty, Form) ->
    ?LOG_TRACE("Checking form ~1000p~nagainst type ~1000p", Form, Ty),
    % The type has the form as specified in ast_erl
    R = case Ty of
        {ann_type, _, [_, Ty2]} -> check_ty(Spec, CurModule, Ty2, Form);
        {atom, _, Atom} -> Atom =:= Form;
        {integer, _, Int} -> Int =:= Form;
        {char, _, Char} -> Char =:= Form;
        {type, _, binary, [{integer, _, _I1}, {integer, _, _I2}]} ->
            errors:not_implemented("Checking of types for bitstrings not implemented");
        {type, _, nil, []} -> Form =:= [];
        {type, _, list, [Ty2]} ->
            is_list(Form) andalso lists:all(fun (X) -> check_ty(Spec, CurModule, Ty2, X) end, Form);
        {type, _, 'fun', _} ->
            utils:error("Cannot check form against function type ~p", Ty);
        {type, _, bounded_fun, [_, _]} ->
            utils:error("Cannot check form against function type ~p", Ty);
        {type, _, range, [{integer, _, _I1}, {integer, _, _I2}]} ->
            errors:not_implemented("Checking of types for integer ranges not implemented: ~p");
        {type, _, map, any} ->
            #{} =:= Form;
        {type, Anno, map, TyAssocs} ->
                case
                    try maps:to_list(Form)
                    catch {badmap, _} -> false
                    end
                of
                    false -> false;
                    List ->
                        % don't care about required files
                        KeyTy = {type, Anno, union,
                                 lists:map(fun({type, _, _, [K, _]}) -> K end, TyAssocs)},
                        ValTy = {type, Anno, union,
                                 lists:map(fun({type, _, _, [_, V]}) -> V end, TyAssocs)},
                        KvTy = {type, Anno, tuple, [KeyTy, ValTy]},
                        TotalTy = {type, Anno, list, [KvTy]},
                        check_ty(Spec, CurModule, TotalTy, List)
                end;
        {op, _, _, _, _} ->
            utils:error("Checking of types with binary operators not implemented: ~p", Ty);
        {op, _, _, _} ->
            utils:error("Checking of types with unary operators not implemented: ~p", Ty);
        {type, _, any, []} -> true;
        {type, _, term, []} -> true;
        {type, _, none, []} -> false;
        {type, _, no_return, []} -> false;
        {type, _, pid, []} -> is_pid(Form);
        {type, _, port, []} -> is_port(Form);
        {type, _, reference, []} -> is_reference(Form);
        {type, _, float, []} -> is_float(Form);
        {type, _, integer, []} -> is_integer(Form);
        {type, _, arity, []} -> is_integer(Form) andalso Form >= 0 andalso Form < 256;
        {type, _, char, []} -> utils:is_char(Form);
        {type, _, atom, []} -> is_atom(Form);
        {type, _, boolean, []} -> is_boolean(Form);
        {type, _, string, []} -> utils:is_string(Form);
        {type, _, record, _} ->
            utils:error("Checking of types with records not implemented: ~p", Ty);
        {remote_type, _, [{atom, _, RemoteMod}, {atom, _, Name}, Args]} ->
                case {RemoteMod, Name, Args} of
                    {sets, set, [Ty2]} ->
                        sets:is_set(Form) andalso
                        lists:all(fun (X) -> check_ty(Spec, CurModule, Ty2, X) end,
                                  sets:to_list(Form));
                    _ ->
                        Ty3 = lookup_ty(Spec, RemoteMod, Name, Args),
                        report_result(RemoteMod, Name, Form, check_ty(Spec, RemoteMod, Ty3, Form))
                end;
        {type, _,tuple, any} ->
            is_tuple(Form);
        {type, _, tuple, Tys} ->
           is_tuple(Form) andalso check_tys(Spec, CurModule, Tys, tuple_to_list(Form));
        {var, _, Name} ->
            utils:error("Found free type variable ~p", Name);
        {type, _, union, Tys} ->
            X = lists:any(fun (X) -> check_ty(Spec, CurModule, X, Form) end, Tys),
            if not X -> ?LOG_TRACE("Form not valid wrt type.~nForm: ~200p~nType: ~200p", Form, Ty);
               true -> ok
            end,
            X;
        {user_type, _, Name, Args} ->
            Ty2 = lookup_ty(Spec, CurModule, Name, Args),
            report_result(CurModule, Name, Form, check_ty(Spec, CurModule, Ty2, Form));
        _ -> utils:error("unsupported type: ~p", Ty)
    end,
    R.

-spec check_tys(ty_map(), module_name(), [ast_erl:ty()], [term()]) -> boolean().
check_tys(Spec, CurModule, Tys, Forms) ->
    length(Tys) =:= length(Forms) andalso
        lists:all(fun ({Ty, F}) -> check_ty(Spec, CurModule, Ty, F) end, lists:zip(Tys, Forms)).

-spec is_reportable_type(atom(), atom()) -> boolean().
is_reportable_type(Mod, Name) ->
    case {Mod, Name} of
        {ast, form} -> true;
        _ -> false
    end.

-spec report_result(atom(), atom(), term(), boolean()) -> boolean().
report_result(ModName, TyName, Form, Result) ->
    if Result -> Result;
       true ->
            B = is_reportable_type(ModName, TyName),
            if B -> ?LOG_INFO("Term not valid wrt type ~w:~w:~n~200p", ModName, TyName, Form);
               true -> ok
            end,
            Result
    end.

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
    ?assertEqual(mk_test_ty(TyArg), lookup_ty(M, ast_erl, 'gen_funcall', [TyArg])).

lookup_ty_realworld_test() ->
    Forms = parse:parse_file_or_die("src/ast_erl.erl"),
    M = prepare_spec(ast_erl, Forms),
    ?LOG_TRACE("Forms = ~p", Forms),
    ?LOG_TRACE("M = ~p", M),
    TyArg = {user_type, {1,1}, guard_test,[]},
    T = lookup_ty(M, ast_erl, 'gen_funcall', [TyArg]),
    ?assertMatch({type, _, tuple, _}, T).

check_realworld_test() ->
    Forms = parse:parse_file_or_die("src/ast_erl.erl"),
    M = prepare_spec(ast_erl, Forms),
    true = check(M, ast_erl, "test_files/ast_check_test.erl").

check_against(TyName, X) ->
    Forms = parse:parse_file_or_die("src/ast_erl.erl"),
    M = prepare_spec(ast_erl, Forms),
    Ty = lookup_ty(M, ast_erl, TyName, []),
    true = check_ty(M, ast_erl, Ty, X).

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
