-module(ast_check).

% @doc This module checks that the parse tree of some file is covered ty the type
% specs in the ast module. We do this check to make sure our definitions in ast
% are correct. See function check/3.

-include("log.hrl").
-include("parse.hrl").

-export([
    check/3,
    check/4,
    check_against_type/4,
    parse_spec/1,
    parse_spec/2,
    merge_specs/1
]).
-export_type([ty_map/0]).

-ifdef(TEST).
-export([
    prepare_spec/2,
    inst_ty/3,
    lookup_ty_or_die/4
   ]).
-endif.

-include("etylizer.hrl").


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

-spec prepare_spec(module_name(), [ast_erl:form()]) -> ty_map().
prepare_spec(Module, Forms) ->
    Insert = fun (Form, M) ->
        case Form of
            {attribute, _, Kind, {Name, Ty, Args}} when Kind =:= type; Kind =:= opaque; Kind =:= nominal ->
                maps:put({Module, Name, length(Args)},
                         {lists:map(fun(X) -> ast_erl:ty_varname(X) end, Args), Ty}, M);
            _ -> M
        end
    end,
    lists:foldl(Insert, maps:new(), Forms).

-spec parse_spec(file:filename()) -> {ty_map(), module_name()}.
parse_spec(Path) -> parse_spec(Path, #parse_opts{}).

-spec parse_spec(file:filename(), parse_opts()) -> {ty_map(), module_name()}.
parse_spec(Path, Opts) ->
    Module = list_to_atom(filename:basename(Path, ".erl")),
    SpecForms = parse:parse_file_or_die(Path, Opts),
    Spec = prepare_spec(Module, SpecForms),
    SpecWithDeps = merge_specs([Spec | otp_dep_specs()]),
    {SpecWithDeps, Module}.

-spec otp_dep_specs() -> [ty_map()].
otp_dep_specs() ->
    ErlAnnoPath = filename:join([utils:assert_no_error(code:lib_dir(stdlib)), "src", "erl_anno.erl"]),
    ErlAnnoForms = parse:parse_file_or_die(ErlAnnoPath),
    [prepare_spec(erl_anno, ErlAnnoForms)].

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
            % replacing type variables by types yields a type again
            ?assert_type(utils:everywhere(Replace, Ty), ast_erl:ty())
    end.

-spec check_against_type(ty_map(), module_name(), ast_erl:ty() | atom(), term()) -> boolean().
check_against_type(Spec, Module, TyOrTyName, Term) ->
    ResolvedTy = resolve_ty(Spec, Module, TyOrTyName),
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

% A type as it is, and the type that a name without arguments stands for.
-spec resolve_ty(ty_map(), module_name(), ast_erl:ty() | atom()) -> ast_erl:ty().
resolve_ty(Spec, Module, Name) when is_atom(Name) ->
    case lookup_ty(Spec, Module, Name, []) of
        error -> ?ABORT("Cannot resolve type ~w", Name);
        {ok, X} -> X
    end;
resolve_ty(_Spec, _Module, Ty) -> Ty.

% The elements of a list, a term that is no proper list does not have the type.
-spec elements(ast_erl:ty(), term(), integer()) -> [term()].
elements(Ty, Form, Depth) ->
    case utils:proper_list(Form) of
        {ok, L} -> L;
        error -> raise(Ty, Form, Depth)
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
        % the value of an exception has no type: raise/3 and raise_unless/4 throw this triple
        throw:{ast_check_error, X} -> ?assert_type(X, {ast_erl:ty(), term(), integer()})
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
            utils:error("Checking of types for bitstrings not implemented: ~p", Ty);
        {type, _, nil, []} -> raise_unless(Form =:= [], Ty, Form, Depth);
        {type, _, list, [Ty2]} ->
            lists:foreach(fun (X) -> check_ty(Spec, CurModule, Ty2, X, Depth + 1) end,
                          elements(Ty, Form, Depth)),
            ok;
        {type, _, nonempty_list, [Ty2]} ->
            raise_unless(Form =/= [], Ty, Form, Depth),
            lists:foreach(fun (X) -> check_ty(Spec, CurModule, Ty2, X, Depth + 1) end,
                          elements(Ty, Form, Depth)),
            ok;
        {type, _, 'fun', _} ->
            utils:error("Cannot check term against function type ~p", Ty);
        {type, _, bounded_fun, [_, _]} ->
            utils:error("Cannot check term against function type ~p", Ty);
        {type, _, range, [{integer, _, _I1}, {integer, _, _I2}]} ->
            utils:error("Checking of types for integer ranges not implemented: ~p", Ty);
        {type, _, map, any} ->
            raise_unless({} =:= Form, Ty, Form, Depth);
        {type, Anno, map, TyAssocs} when is_list(TyAssocs) ->
                case Form of
                    _ when not is_map(Form) -> raise(Ty, Form, Depth);
                    _ ->
                        List = maps:to_list(Form),
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
            utils:error("Checking of types with binary operators not implemented: ~p", Ty);
        {op, _, _, _} ->
            utils:error("Checking of types with unary operators not implemented: ~p", Ty);
        {type, _, any, []} -> ok;
        {type, _, term, []} -> ok;
        {type, _, none, []} -> raise(Ty, Form, Depth);
        {type, _, no_return, []} -> raise(Ty, Form, Depth);
        {type, _, pid, []} -> raise_unless(is_pid(Form), Ty, Form, Depth);
        {type, _, port, []} -> raise_unless(is_port(Form), Ty, Form, Depth);
        {type, _, reference, []} -> raise_unless(is_reference(Form), Ty, Form, Depth);
        {type, _, float, []} -> raise_unless(is_float(Form), Ty, Form, Depth);
        {type, _, integer, []} -> raise_unless(is_integer(Form), Ty, Form, Depth);
        {type, _, non_neg_integer, []} ->
            raise_unless(is_integer(Form) andalso Form >= 0, Ty, Form, Depth);
        {type, _, pos_integer, []} ->
            raise_unless(is_integer(Form) andalso Form >= 1, Ty, Form, Depth);
        {type, _, neg_integer, []} ->
            raise_unless(is_integer(Form) andalso Form < 0, Ty, Form, Depth);
        {type, _, arity, []} ->
            raise_unless(is_integer(Form) andalso Form >= 0 andalso Form < 256, Ty, Form, Depth);
        {type, _, char, []} -> raise_unless(utils:is_char(Form), Ty, Form, Depth);
        {type, _, atom, []} -> raise_unless(is_atom(Form), Ty, Form, Depth);
        {type, _, boolean, []} -> raise_unless(is_boolean(Form), Ty, Form, Depth);
        {type, _, string, []} -> raise_unless(utils:is_string(Form), Ty, Form, Depth);
        {type, _, record, _} ->
            utils:error("Checking of types with records not implemented: ~p", Ty);
        {remote_type, _, [{atom, _, RemoteMod}, {atom, _, Name}, Args]} ->
                case {RemoteMod, Name, Args} of
                    {etylizer, cons, [HdTy, TlTy]} ->
                        case Form of
                            [Hd | Tl] ->
                                check_ty(Spec, CurModule, HdTy, Hd, Depth + 1),
                                check_ty(Spec, CurModule, TlTy, Tl, Depth + 1);
                            _ -> raise(Ty, Form, Depth)
                        end;
                    {etylizer, without, [Ty1, Ty2]} ->
                        check_ty(Spec, CurModule, Ty1, Form, Depth + 1),
                        raise_unless(check_ty_with_result(Spec, CurModule, Ty2, Form, Depth + 1) =/= ok,
                                     Ty, Form, Depth);
                    {sets, set, [Ty2]} ->
                        raise_unless(sets:is_set(Form), Ty, Form, Depth),
                        % a term that sets:is_set/1 has just accepted: there is no type test for a set
                        lists:foreach(fun (X) -> check_ty(Spec, CurModule, Ty2, X, Depth + 1) end,
                                  sets:to_list(?assert_type(Form, sets:set(term())))),
                        ok;
                    _ ->
                        Ty3 = lookup_ty_or_die(Spec, RemoteMod, Name, Args),
                        check_ty(Spec, RemoteMod, Ty3, Form, Depth)
                end;
        {type, _,tuple, any} ->
            raise_unless(is_tuple(Form), Ty, Form, Depth);
        {type, _, tuple, Tys} when is_list(Tys) ->
            FormList = case Form of
                _ when is_tuple(Form) -> tuple_to_list(Form);
                _ -> raise(Ty, Form, Depth)
            end,
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
                    Errors = [E || E = {_, _, _} <- Results],
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

