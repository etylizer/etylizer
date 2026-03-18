-module(pretty).

-compile([nowarn_shadow_vars]).


-export([
         arity/2,
%         constr/1,
%         substs/1,
%         subst/1,
         constr_block/1,
         loc/1,
%         locs/1,
         atom/1,
         render/1,
         render_ty/1,
         render_tys/1,
         render_tyscheme/1,
         render_constr/1,
         render_substs/1,
         render_subst/1,
         render_mono_env/1,
         render_poly_env/1,
         render_fun_env/1,
         render_op_env/1,
         render_record_env/1,
         render_ty_env/1,
         render_any_ref/1,
         render_var/1,
         render_set/2,
         render_list/2,
%         pretty_list/2,
%         render_list_with_braces/2,
         ref/1,
         render_varnames/1,
         render_exps/2
        ]).

-ifdef(TEST).
-export([
    ty/1,
    tyscheme/1
]).
-endif.

-import(prettypr, [text/1]).

-include("etylizer.hrl").

-type doc() :: prettypr:document().

-spec parens(doc()) -> doc().
parens(D) -> beside(text("("), D, text(")")).

-spec brackets(doc()) -> doc().
brackets(D) -> beside(text("{"), D, text("}")).

-spec braces(doc()) -> doc().
braces(D) -> beside(text("["), D, text("]")).

-spec comma(doc(), doc()) -> doc().
comma(D1, D2) -> comma_sep([D1, D2]).

-spec beside(doc(), doc()) -> doc().
beside(D1, D2) ->
    case is_list(D1) of
        false -> prettypr:beside(D1, D2);
        true -> errors:bug("beside called with list argument ~w", [D1])
    end.

-spec beside(doc(), doc(), doc()) -> doc().
beside(D1, D2, D3) -> beside(D1, beside(D2, D3)).

-spec beside(doc(), doc(), doc(), doc()) -> doc().
beside(D1, D2, D3, D4) -> beside(D1, beside(D2, beside(D3, D4))).

-spec beside(doc(), doc(), doc(), doc(), doc()) -> doc().
beside(D1, D2, D3, D4, D5) -> beside(D1, beside(D2, beside(D3, beside(D4, D5)))).

-spec comma_sep(list(doc())) -> doc().
comma_sep(L) -> sep_by(text(","), L).

% Automatically appends a spac or a newline character to Sep.
-spec sep_by(doc(), list(doc())) -> doc().
sep_by(_Sep, []) -> text("");
sep_by(_Sep, [D]) -> D;
sep_by(Sep, Docs) ->
    WithSep =
        lists:foldr(
          fun(D, Acc) ->
                  case Acc of
                      [] -> [D]; % last without trailing sep
                      _ -> [beside(D, Sep) | Acc]
                  end
          end,
          [],
          Docs),
    Res = prettypr:sep(WithSep),
    Res.

-spec render(doc()) -> string().
render(D) ->
    prettypr:format(D, 200).

-spec render_ty(ast:ty()) -> string().
render_ty(T) -> render(ty(T)).

-spec render_tys([ast:ty()]) -> string().
render_tys(T) -> render(tys(T)).

-spec render_tyscheme(ast:ty_scheme()) -> string().
render_tyscheme(T) -> render(tyscheme(T)).

-spec render_constr(all_constrs()) -> string().
render_constr(C) -> render(constr(C)).

-spec render_substs([subst:t()]) -> string().
render_substs(S) -> render(substs(S)).

-spec render_subst(subst:t()) -> string().
render_subst(S) -> render(subst(S)).

-spec render_poly_env(constr:constr_poly_env()) -> string().
render_poly_env(S) -> render(poly_env(S)).

-spec render_mono_env(constr:constr_env()) -> string().
render_mono_env(S) -> render(mono_env(S)).

-spec render_fun_env(symtab:fun_env()) -> string().
render_fun_env(S) -> render(fun_env(S)).

-spec render_ty_env(symtab:ty_env()) -> string().
render_ty_env(S) -> render(ty_env(S)).

-spec render_op_env(symtab:op_env()) -> string().
render_op_env(S) -> render(op_env(S)).

-spec render_record_env(symtab:record_env()) -> string().
render_record_env(S) -> render(record_env(S)).

-spec render_any_ref(ast:any_ref()) -> string().
render_any_ref(R) -> render(ref(R)).

-spec render_var(ast:exp_var()) -> string().
render_var(R) -> render(var(R)).

-spec atom(atom()) -> doc().
atom(A) -> text(atom_to_list(A)).

-spec integer(integer()) -> doc().
integer(I) -> text(integer_to_list(I)).

-spec tyscheme(ast:ty_scheme()) -> doc().
tyscheme({ty_scheme, [], Ty}) -> ty(Ty);
tyscheme({ty_scheme, Vars, Ty}) ->
    PrettyBound =
        fun({Name, Bound}) ->
                NameDoc = atom(Name),
                case Bound of
                    {predef, any} -> NameDoc;
                    _ -> beside(NameDoc, text(" :: "), ty(Bound))
                end
        end,
    beside(text("FORALL "), comma_sep(lists:map(PrettyBound, Vars)),
           text(" . "), ty(Ty)).

-spec tys([ast:ty()])-> doc().
tys(Ts) ->
    comma_sep(lists:map(fun ty/1, Ts)).

-spec ty(ast:ty()) -> doc().
ty(T) -> ty(1, T).

-spec ty(integer(), ast:ty()) -> doc().
ty(Prec, T) ->
    case T of
        {singleton, A} ->
            case A of
                _ when is_atom(A) -> atom(A);
                _ when is_integer(A) -> integer(A) % char() is a subtype of integer()
            end;
        {bitstring} ->
            text("bitstring()");
        % {binary, I, J} ->
        %     text(utils:sformat("<<_:~w, _:_*~w>>", I, J));
        {binary, M, N} ->
            text(utils:sformat("<<_:~w, _:_*~w>>", M, N));
        {empty_list} ->
            text("[]");
        {fun_simple} ->
            text("fun()");
        {range, '*', '*'} ->
            text("integer()");
        {range, '*', J} ->
            text(utils:sformat("..~w", J));
        {range, I, '*'} ->
            text(utils:sformat("~w..", I));
        {range, I, J} ->
            text(utils:sformat("~w..~w", I, J));
        {map_any} ->
            text("#{}");
        {predef, Name} ->
            beside(atom(Name), text("()"));
        {predef_alias, Name} ->
            beside(atom(Name), text("()"));
        {tuple_any} ->
            text("tuple()");
        {mu_var, Name} ->
            beside(text("mu "), atom(Name));
        {var, Name} ->
            atom(Name);
        _ -> ty_list_or_fun(Prec, T)
    end.

-spec ty_list_or_fun(integer(), ast:ty()) -> doc().
ty_list_or_fun(Prec, T) ->
    case T of
        {cons, A, B} ->
            beside(text("["), ty(A), text(" @ "), ty(B), text("]"));
        {list, U} ->
            beside(text("list("), ty(U), text(")"));
        {nonempty_list, U} ->
            beside(text("nonempty_list"), parens(ty(U)));
        {improper_list, U, V} ->
            beside(text("improper_list"), parens(comma(ty(U), ty(V))));
        {nonempty_improper_list, U, V} ->
            beside(text("nonempty_improper_list"), parens(comma(ty(U), ty(V))));
        {fun_any_arg, U} ->
            beside(text("fun((...) -> "), ty(U), text(")"));
        {fun_full, Args, Res} ->
            beside(text("fun"),
                   parens(beside(
                            parens(comma_sep(lists:map(fun ty/1, Args))),
                            text(" -> "),
                            ty(Res))));
        _ -> ty_composite(Prec, T)
    end.

-spec ty_composite(integer(), ast:ty()) -> doc().
ty_composite(Prec, T) ->
    case T of
        {map, Assocs} ->
            AssocsP =
                lists:map(
                  fun(A) ->
                          case A of
                              {map_field_opt, U, V} ->
                                  beside(ty(U), text(" => "), ty(V));
                              {map_field_req, U, V} ->
                                  beside(ty(U), text(" := "), ty(V))
                          end
                  end,
                  Assocs
                 ),
            beside(text("#"), brackets(comma_sep(AssocsP)));
        {mu, Var, Ty} ->
            beside(ty(Var), text("."), ty(Ty));
        {named, _Loc, Ref, Args} ->
            RefP =
                case Ref of
                    {ty_ref, _, Name, _} -> atom(Name);
                    {ty_qref, Mod, Name, _} ->
                        beside(atom(Mod), text(":"), atom(Name))
                end,
            beside(RefP, parens(comma_sep(lists:map(fun ty/1, Args))));
        {tuple, Args} ->
            brackets(comma_sep(lists:map(fun ty/1, Args)));
        {union, []} ->
            text("none()");
        {union, Args} ->
            with_parens(Prec >= 2,
                        sep_by(text(" |"), lists:map(fun (T) -> ty(2, T) end, Args)));
        {intersection, []} ->
            text("any()");
        {intersection, Args} ->
            with_parens(Prec >= 3,
                        sep_by(text(" /\\"), lists:map(fun (T) -> ty(3, T) end, Args)));
        {negation, U} ->
            beside(text("not"), parens(ty(U)));
        X -> errors:uncovered_case(?FILE, ?LINE, X)
    end.

-spec with_parens(boolean(), doc()) -> doc().
with_parens(false, D) -> D;
with_parens(true, D) -> parens(D).

-spec var(ast:exp_var()) -> doc().
var({var, _, AnyRef}) -> ref(AnyRef).

-spec arity(atom(), arity()) -> doc().
arity(Name, Arity) -> text(utils:sformat("~w/~w", Name, Arity)).

-spec qarity(atom(), atom(), arity()) -> doc().
qarity(Mod, Name, Arity) -> text(utils:sformat("~w:~w/~w", Mod, Name, Arity)).

-spec ref(ast:any_ref() | ast:ty_ref()) -> doc().
ref(AnyRef) ->
    case AnyRef of
        {ref, Name, Arity} -> arity(Name, Arity);
        {qref, Mod, Name, Arity} -> qarity(Mod, Name, Arity);
        {ty_ref, Mod, Name, Arity} -> qarity(Mod, Name, Arity);
        {ty_qref, Mod, Name, Arity} -> qarity(Mod, Name, Arity);
        {local_ref, {Name, Tok}} ->
            beside(atom(Name), text("@"), text(utils:sformat("~w", Tok)));
        {escaped_ref, {Name, Tok}, _EscTyVar} ->
            beside(atom(Name), text("@"), text(utils:sformat("~w'", Tok)))
    end.

-spec constr_env(constr:constr_env()) -> doc().
constr_env(Env) ->
    beside(text("#{"),
           comma_sep(
             lists:map(
               fun({AnyRef, T}) ->
                       beside(ref(AnyRef), text(" => "), ty(T))
               end,
               maps:to_list(Env))
            ),
           text("}")).

-spec constr_bodies([constr:constr_case_branch()]) -> doc().
constr_bodies(L) ->
    braces(comma_sep(lists:map(fun constr_body/1, L))).

-spec constr_body(constr:constr_case_branch()) -> doc().
constr_body({ccase_branch, Locs, Payload}) ->
    GuardPart = constr_body_guard(Payload),
    BodyPart = constr_body_body(Payload),
    brackets(comma_sep([locs(Locs)] ++ GuardPart ++ BodyPart)).

-spec constr_body_guard(constr:case_branch_payload()) -> [doc()].
constr_body_guard(Payload) ->
    {GuardEnv, GuardCs} = constr:case_branch_guard(Payload),
    [kv("guardEnv", constr_env(GuardEnv)),
     kv("guardCs", constr(GuardCs))].

-spec constr_body_body(constr:case_branch_payload()) -> [doc()].
constr_body_body(Payload) ->
    {BodyEnv, BodyCs} = constr:case_branch_body(Payload),
    [kv("bodyEnv", constr_env(BodyEnv)),
     kv("bodyCs", constr(BodyCs))] ++ constr_body_cond_result(Payload).

-spec constr_body_cond_result(constr:case_branch_payload()) -> [doc()].
constr_body_cond_result(Payload) ->
    ResultCs = constr:case_branch_result(Payload),
    BodyCondCs = constr:case_branch_bodyCond(Payload),
    PrettyBodyCond =
        case BodyCondCs of
            none -> text("none");
            X -> constr(X)
        end,
    [kv("bodyCond", PrettyBodyCond),
     kv("resultCs", constr(ResultCs))].

-spec sconstr_bodies([constr:simp_constr_case_branch()]) -> doc().
sconstr_bodies(L) ->
    braces(comma_sep(lists:map(fun sconstr_body/1, L))).

-spec sconstr_body(constr:simp_constr_case_branch()) -> doc().
sconstr_body({sccase_branch, {GuardsLoc, Guards}, Cond, {BodyLoc, Body}, {ResultLoc, Result}}) ->
    GuardPart = [kv("guardLoc", loc(GuardsLoc)), kv("guard", constr(Guards))],
    CondPart = sconstr_body_cond(Cond),
    BodyPart = sconstr_body_rest(BodyLoc, Body, ResultLoc, Result),
    brackets(comma_sep(GuardPart ++ CondPart ++ BodyPart)).

-spec sconstr_body_cond(none | {ast:loc(), constr:simp_constrs()}) -> [doc()].
sconstr_body_cond(none) -> [text("none")];
sconstr_body_cond({L2, X}) -> [kv("condLoc", loc(L2)), kv("cond", constr(X))].

-spec sconstr_body_rest(ast:loc(), constr:simp_constrs(), ast:loc(), constr:simp_constrs()) -> [doc()].
sconstr_body_rest(BodyLoc, Body, ResultLoc, Result) ->
    [kv("bodyLoc", loc(BodyLoc)),
     kv("body", constr(Body)),
     kv("resultLoc", loc(ResultLoc)),
     kv("result", constr(Result))].

-spec kv(string(), doc()) -> doc().
kv(K, V) -> beside(text(K), text(":"), V).

-type all_constrs() :: constr:simp_constr() | constr:constr()
                     | sets:set(all_constrs()) | list(all_constrs()).

-spec constr(all_constrs()) -> doc().
constr(X) when is_list(X) ->
    constr_list(X);
constr(X) ->
    case sets:is_set(X) of
        true ->
            constr_set(?assert_type(X, sets:set(all_constrs())));
        false ->
            constr_single(?assert_type(X, constr:simp_constr() | constr:constr()))
    end.

-spec constr_list(list(all_constrs())) -> doc().
constr_list(X) ->
    brackets(comma_sep(lists:map(fun constr/1, X))).

-spec constr_set(sets:set(all_constrs())) -> doc().
constr_set(X) ->
    braces(comma_sep(lists:map(fun constr/1, sets:to_list(X)))).

-spec constr_single(constr:simp_constr() | constr:constr()) -> doc().
constr_single({scsubty, _, _, _} = X) -> constr_simp(?assert_type(X, constr:simp_constr()));
constr_single({sccase, _, _, _} = X) -> constr_simp(?assert_type(X, constr:simp_constr()));
constr_single({scmater, _, _, _} = X) -> constr_simp(?assert_type(X, constr:simp_constr()));
constr_single(X) -> constr_unsimplified(?assert_type(X, constr:constr())).

-spec constr_unsimplified(constr:constr()) -> doc().
constr_unsimplified({csubty, _, _, _} = X) -> constr_leaf(X);
constr_unsimplified({cvar, _, _, _} = X) -> constr_leaf(X);
constr_unsimplified({cvarmater, _, _, _} = X) -> constr_leaf(X);
constr_unsimplified(X) -> constr_nested(X).

-spec constr_leaf(constr:constr_subty() | constr:constr_var() | constr:constr_var_mater()) -> doc().
constr_leaf({csubty, Locs, T1, T2}) ->
    brackets(comma_sep([text("csubty"),
                        locs(Locs),
                        ty(T1),
                        ty(T2)]));
constr_leaf({cvar, Locs, Ref, T}) ->
    brackets(comma_sep([text("cvar"),
                        locs(Locs),
                        ref(Ref),
                        ty(T)]));
constr_leaf({cvarmater, Locs, Ref, Alpha}) ->
    brackets(comma_sep([text("cvarmater"),
                        locs(Locs),
                        ref(Ref),
                        text(atom_to_list(Alpha))])).

-spec constr_nested(constr:constr_op() | constr:constr_def() | constr:constr_case()) -> doc().
constr_nested({cop, Locs, Name, Arity, T}) ->
    brackets(comma_sep([text("cop"),
                        locs(Locs),
                        beside(atom(Name), text("/"), text(integer_to_list(Arity))),
                        ty(T)]));
constr_nested({cdef, _, _, _} = X) -> constr_cdef(X);
constr_nested({ccase, _, _, _, _} = X) -> constr_ccase(X).

-spec constr_cdef(constr:constr_def()) -> doc().
constr_cdef({cdef, Locs, Env, Cs}) ->
    brackets(comma_sep([text("cdef"),
                        locs(Locs),
                        constr_env(Env),
                        constr(Cs)])).

-spec constr_ccase(constr:constr_case()) -> doc().
constr_ccase({ccase, Locs, CsScrut, CsExhaust, Bodies}) ->
    brackets(comma_sep([text("ccase"),
                        locs(Locs),
                        kv("scrutiny", constr(CsScrut)),
                        kv("exhaust", constr(CsExhaust)),
                        constr_bodies(Bodies)])).

-spec constr_simp(constr:simp_constr()) -> doc().
constr_simp({scsubty, Loc, T1, T2}) ->
    brackets(comma_sep([text("scsubty"),
                        loc(Loc),
                        ty(T1),
                        ty(T2)]));
constr_simp({sccase, _, _, _} = X) -> constr_sccase(X);
constr_simp({scmater, Loc, T, Alpha}) ->
    brackets(comma_sep([text("scmater"),
                        loc(Loc),
                        ty(T),
                        text(atom_to_list(Alpha))])).

-spec constr_sccase(constr:simp_constr_case()) -> doc().
constr_sccase({sccase, {LocScrut, CsScrut}, {LocExhaust, CsExhaust}, Bodies}) ->
    brackets(comma_sep([text("sccase"),
                        kv("scrutinyLoc", loc(LocScrut)),
                        kv("scrutiny", constr(CsScrut)),
                        kv("exhaustLoc", loc(LocExhaust)),
                        kv("exhaust", constr(CsExhaust)),
                        sconstr_bodies(Bodies)])).

-spec locs(constr:locs()) -> doc().
locs({Msg, Locs}) ->
    beside(text(utils:sformat("~p", Msg)), text(":"),
           case sets:to_list(Locs) of
               [] -> text("NO_LOC");
               [L] -> loc(L);
               More -> braces(comma_sep(lists:map(fun loc/1, More)))
           end).

-spec loc(ast:loc()) -> doc().
loc({loc, _, Line,Col}) -> text(utils:sformat("~w:~w", Line, Col)).

-spec substs([subst:t()]) -> doc().
substs(L) ->
    brackets(comma_sep(lists:map(fun subst/1, L))).

-spec subst(subst:t()) -> doc().
subst({tally_subst, S, Fixed}) ->
    PrettyS = subst(S),
    PrettyFixed = braces(comma_sep(lists:map(fun atom/1, sets:to_list(Fixed)))),
    brackets(comma_sep([text("tally_subst"), PrettyS, PrettyFixed]));
subst(S) ->
    Elems =
        lists:map(
          fun({V, T}) ->
                 beside(atom(V),
                        text(" => "),
                        ty(T))
          end,
          maps:to_list(subst:base_subst(S))),
    brackets(comma_sep(Elems)).

-spec pretty_map(fun((K) -> doc()), fun((V) -> doc()), #{K => V}) -> doc().
pretty_map(FK, FV, M) ->
    Elems =
        lists:map(
          fun({Ref, T}) ->
                 beside(FK(Ref),
                        text(" => "),
                        FV(T))
          end,
          maps:to_list(M)),
    brackets(comma_sep(Elems)).

-spec poly_env(constr:constr_poly_env()) -> doc().
poly_env(Env) ->
    pretty_map(fun ref/1, fun tyscheme/1, Env).

-spec fun_env(symtab:fun_env()) -> doc().
fun_env(Env) -> poly_env(Env).

-spec ty_env(symtab:ty_env()) -> doc().
ty_env(Env) ->
    pretty_map(
        fun ({ty_key, Mod, Name, Arity}) ->
            beside(atom(Mod), text(":"), atom(Name), text("/"), integer(Arity)) end,
            fun tyscheme/1,
            Env).

-spec op_env(symtab:op_env()) -> doc().
op_env(Env) ->
    pretty_map(fun({OpName, Arity}) -> arity(OpName, Arity) end, fun tyscheme/1, Env).

-spec record_env(symtab:record_env()) -> doc().
record_env(Env) ->
    pretty_map(
        fun(RecName) -> atom(RecName) end,
        fun({_RecName, Fields}) ->
            pretty_list(
                fun({FieldName, FieldTy}) ->
                    beside(atom(FieldName), text(" :: "), ty(FieldTy))
                end,
                Fields)
        end,
        Env).

-spec mono_env(constr:constr_env()) -> doc().
mono_env(Env) ->
    Elems =
        lists:map(
          fun({Ref, T}) ->
                 beside(ref(Ref),
                        text(" => "),
                        ty(T))
          end,
          maps:to_list(Env)),
    brackets(comma_sep(Elems)).

-spec constr_block(constr_error_locs:constr_block()) -> doc().
constr_block({Kind, Loc, What, Ds}) ->
    brackets(comma_sep([atom(Kind),
                        loc(Loc),
                        text(What),
                        constr(Ds)])).

-spec pretty_list(fun((T) -> doc()), list(T)) -> doc().
pretty_list(Fun, L) ->
    comma_sep(lists:map(Fun, L)).

-spec render_list(fun((T) -> doc()), list(T)) -> string().
render_list(Fun, L) ->
    render(pretty_list(Fun, L)).

-spec render_set(fun((T) -> doc()), sets:set(T)) -> string().
render_set(Fun, S) ->
    render_list(Fun, sets:to_list(S)).

% --- Pretty-printing for transformed AST expressions ---

-spec render_varnames([ast:local_varname()]) -> string().
render_varnames(Vars) ->
    string:join([varname(V) || V <- Vars], ", ").

-spec render_exps([ast:exp()], non_neg_integer()) -> string().
render_exps(Exps, Indent) ->
    Pad = lists:duplicate(Indent, $\s),
    string:join([Pad ++ render_exp(E, Indent) || E <- Exps], ",\n").

-spec varname(ast:local_varname()) -> string().
varname({Name, _Tok}) -> atom_to_list(Name).

-spec render_exp(ast:exp(), non_neg_integer()) -> string().
render_exp(Exp, Indent) ->
    case Exp of
        {atom, _, A} -> atom_to_list(A);
        {integer, _, I} -> integer_to_list(I);
        {char, _, C} -> [$ | [C]];
        {float, _, F} -> float_to_list(F);
        {string, _, S} -> io_lib:format("~p", [S]);
        {var, _, {local_ref, V}} -> varname(V);
        {var, _, {local_bind, V}} -> varname(V);
        {var, _, {ref, N, _A}} -> atom_to_list(N);
        {var, _, {qref, M, N, _A}} -> utils:sformat("~w:~w", M, N);
        {var, _, {escaped_ref, V, _TyVar}} -> varname(V);
        {wildcard, _} -> "_";
        {tuple, _, Elems} ->
            "{" ++ string:join([render_exp(E, Indent) || E <- Elems], ", ") ++ "}";
        {cons, _, H, T} ->
            "[" ++ render_exp(H, Indent) ++ " | " ++ render_exp(T, Indent) ++ "]";
        {nil, _} -> "[]";
        {'case', _, Scrut, Clauses, _EscAnn} ->
            render_case(Scrut, Clauses, Indent);
        {'case', _, Scrut, Clauses} ->
            render_case(Scrut, Clauses, Indent);
        {call, _, Fun, Args} ->
            render_exp(Fun, Indent) ++ "(" ++
            string:join([render_exp(A, Indent) || A <- Args], ", ") ++ ")";
        {call_remote, _, Mod, Fun, Args} ->
            render_exp(Mod, Indent) ++ ":" ++ render_exp(Fun, Indent) ++ "(" ++
            string:join([render_exp(A, Indent) || A <- Args], ", ") ++ ")";
        {op, _, Op, L, R} ->
            render_exp(L, Indent) ++ " " ++ atom_to_list(Op) ++ " " ++ render_exp(R, Indent);
        {op, _, Op, [Operand]} ->
            atom_to_list(Op) ++ render_exp(Operand, Indent);
        {op, _, Op, Operand} when is_tuple(Operand) ->
            atom_to_list(Op) ++ render_exp(Operand, Indent);
        {'fun', _, Name, Clauses} ->
            Pad = lists:duplicate(Indent, $\s),
            Inner = Indent + 2,
            InPad = lists:duplicate(Inner, $\s),
            NameStr = case Name of
                no_name -> "";
                {local_bind, V} -> varname(V)
            end,
            "fun " ++ NameStr ++ "\n" ++
            string:join([InPad ++ render_fun_clause(C, Inner) || C <- Clauses], ";\n") ++ "\n" ++
            Pad ++ "end";
        {fun_ref, _, Ref} -> "fun " ++ render(ref(Ref));
        {fun_ref_dyn, _, {global_ref_dyn, Mod, Fun, Arity}} ->
            "fun " ++ render_exp(Mod, Indent) ++ ":" ++ render_exp(Fun, Indent) ++
            "/" ++ render_exp(Arity, Indent);
        {block, _, Exps} ->
            "begin " ++ string:join([render_exp(E, Indent) || E <- Exps], ", ") ++ " end";
        {match, _, Pat, E} ->
            render_exp(Pat, Indent) ++ " = " ++ render_exp(E, Indent);
        {'catch', _, E} ->
            "catch " ++ render_exp(E, Indent);
        {'if', _, Clauses} ->
            Pad = lists:duplicate(Indent, $\s),
            Inner = Indent + 2,
            InPad = lists:duplicate(Inner, $\s),
            "if\n" ++
            string:join([InPad ++ render_if_clause(C, Inner) || C <- Clauses], ";\n") ++ "\n" ++
            Pad ++ "end";
        {'receive', _, Clauses} ->
            Pad = lists:duplicate(Indent, $\s),
            Inner = Indent + 2,
            InPad = lists:duplicate(Inner, $\s),
            "receive\n" ++
            string:join([InPad ++ render_clause(C, Inner) || C <- Clauses], ";\n") ++ "\n" ++
            Pad ++ "end";
        {receive_after, _, Clauses, Timeout, AfterBody} ->
            Pad = lists:duplicate(Indent, $\s),
            Inner = Indent + 2,
            InPad = lists:duplicate(Inner, $\s),
            ClausesStr = case Clauses of
                [] -> "";
                _ -> string:join([InPad ++ render_clause(C, Inner) || C <- Clauses], ";\n") ++ "\n"
            end,
            "receive\n" ++ ClausesStr ++
            Pad ++ "after " ++ render_exp(Timeout, Indent) ++ " ->\n" ++
            string:join([InPad ++ render_exp(E, Inner) || E <- AfterBody], ",\n") ++ "\n" ++
            Pad ++ "end";
        {'try', _, Exps, Cases, Catches, After} ->
            Pad = lists:duplicate(Indent, $\s),
            Inner = Indent + 2,
            InPad = lists:duplicate(Inner, $\s),
            ExpsStr = string:join([InPad ++ render_exp(E, Inner) || E <- Exps], ",\n"),
            CasesStr = case Cases of
                [] -> "";
                _ -> " of\n" ++
                    string:join([InPad ++ render_clause(C, Inner) || C <- Cases], ";\n") ++ "\n"
            end,
            CatchesStr = case Catches of
                [] -> "";
                _ -> Pad ++ "catch\n" ++
                    string:join([InPad ++ render_catch_clause(C, Inner) || C <- Catches], ";\n") ++ "\n"
            end,
            AfterStr = case After of
                [] -> "";
                _ -> Pad ++ "after\n" ++
                    string:join([InPad ++ render_exp(E, Inner) || E <- After], ",\n") ++ "\n"
            end,
            "try\n" ++ ExpsStr ++ "\n" ++ CasesStr ++ CatchesStr ++ AfterStr ++ Pad ++ "end";
        {bin, _, Elems} ->
            "<<" ++ string:join([render_bin_element(E, Indent) || E <- Elems], ", ") ++ ">>";
        {map_create, _, Assocs} ->
            "#{" ++ string:join([render_map_assoc(A, Indent) || A <- Assocs], ", ") ++ "}";
        {map_update, _, E, Assocs} ->
            render_exp(E, Indent) ++ "#{" ++
            string:join([render_map_assoc(A, Indent) || A <- Assocs], ", ") ++ "}";
        {map, _, Assocs} ->
            "#{" ++ string:join([render_map_assoc(A, Indent) || A <- Assocs], ", ") ++ "}";
        {lc, _, E, Qualifiers} ->
            "[" ++ render_exp(E, Indent) ++ " || " ++
            string:join([render_qualifier(Q, Indent) || Q <- Qualifiers], ", ") ++ "]";
        {bc, _, E, Qualifiers} ->
            "<<" ++ render_exp(E, Indent) ++ " || " ++
            string:join([render_qualifier(Q, Indent) || Q <- Qualifiers], ", ") ++ ">>";
        {mc, _, Key, Val, Qualifiers} ->
            "#{" ++ render_exp(Key, Indent) ++ " => " ++ render_exp(Val, Indent) ++ " || " ++
            string:join([render_qualifier(Q, Indent) || Q <- Qualifiers], ", ") ++ "}";
        {record_create, _, Name, Fields} ->
            "#" ++ atom_to_list(Name) ++ "{" ++
            string:join([render_record_field(F, Indent) || F <- Fields], ", ") ++ "}";
        {record, _, Name, Fields} ->
            "#" ++ atom_to_list(Name) ++ "{" ++
            string:join([render_record_field(F, Indent) || F <- Fields], ", ") ++ "}";
        {record_field, _, E, Name, Field} ->
            render_exp(E, Indent) ++ "#" ++ atom_to_list(Name) ++ "." ++ atom_to_list(Field);
        {record_index, _, Name, Field} ->
            "#" ++ atom_to_list(Name) ++ "." ++ atom_to_list(Field);
        {record_update, _, E, Name, Fields} ->
            render_exp(E, Indent) ++ "#" ++ atom_to_list(Name) ++ "{" ++
            string:join([render_record_field(F, Indent) || F <- Fields], ", ") ++ "}";
        {annotate, _, E, _Ty} ->
            render_exp(E, Indent);
        {assert, _, E, _Ty} ->
            render_exp(E, Indent);
        _ ->
            io_lib:format("~w", [Exp])
    end.

-spec render_case(ast:exp(), [ast:case_clause()], non_neg_integer()) -> string().
render_case(Scrut, Clauses, Indent) ->
    Pad = lists:duplicate(Indent, $\s),
    Inner = Indent + 2,
    InPad = lists:duplicate(Inner, $\s),
    "case " ++ render_exp(Scrut, Indent) ++ " of\n" ++
    string:join([InPad ++ render_clause(C, Inner) || C <- Clauses], ";\n") ++ "\n" ++
    Pad ++ "end".

-spec render_clause(ast:case_clause(), non_neg_integer()) -> string().
render_clause({case_clause, _, Pat, Guards, Body}, Indent) ->
    PatStr = render_exp(Pat, Indent),
    GuardStr = render_guards(Guards, Indent),
    BodyStr = string:join([render_exp(E, Indent + 2) || E <- Body], ",\n" ++ lists:duplicate(Indent + 2, $\s)),
    PatStr ++ GuardStr ++ " ->\n" ++ lists:duplicate(Indent + 2, $\s) ++ BodyStr.

-spec render_fun_clause(ast:fun_clause(), non_neg_integer()) -> string().
render_fun_clause({fun_clause, _, Pats, Guards, Body}, Indent) ->
    PatStr = "(" ++ string:join([render_exp(P, Indent) || P <- Pats], ", ") ++ ")",
    GuardStr = render_guards(Guards, Indent),
    BodyStr = string:join([render_exp(E, Indent + 2) || E <- Body], ",\n" ++ lists:duplicate(Indent + 2, $\s)),
    PatStr ++ GuardStr ++ " -> " ++ BodyStr.

-spec render_if_clause(ast:if_clause(), non_neg_integer()) -> string().
render_if_clause({if_clause, _, Guards, Body}, Indent) ->
    GuardStr = string:join(
        [string:join([render_exp(G, Indent) || G <- Guard], ", ") || Guard <- Guards], "; "),
    BodyStr = string:join([render_exp(E, Indent + 2) || E <- Body], ",\n" ++ lists:duplicate(Indent + 2, $\s)),
    GuardStr ++ " ->\n" ++ lists:duplicate(Indent + 2, $\s) ++ BodyStr.

-spec render_catch_clause(ast:catch_clause(), non_neg_integer()) -> string().
render_catch_clause({catch_clause, _, ExcType, Pat, Stack, Guards, Body}, Indent) ->
    ExcStr = render_exp(ExcType, Indent),
    PatStr = render_exp(Pat, Indent),
    StackStr = case Stack of
        {wildcard, _} -> "";
        _ -> ":" ++ render_exp(Stack, Indent)
    end,
    GuardStr = render_guards(Guards, Indent),
    BodyStr = string:join([render_exp(E, Indent + 2) || E <- Body], ",\n" ++ lists:duplicate(Indent + 2, $\s)),
    ExcStr ++ ":" ++ PatStr ++ StackStr ++ GuardStr ++ " ->\n" ++
    lists:duplicate(Indent + 2, $\s) ++ BodyStr.

-spec render_guards([ast:guard()], non_neg_integer()) -> string().
render_guards([], _Indent) -> "";
render_guards(Guards, Indent) ->
    " when " ++ string:join(
        [string:join([render_exp(G, Indent) || G <- Guard], ", ") || Guard <- Guards], "; ").

-spec render_bin_element(ast:exp_bitstring_elem(), non_neg_integer()) -> string().
render_bin_element({bin_element, _, Val, Size, TypeSpecifiers}, Indent) ->
    ValStr = render_exp(Val, Indent),
    SizeStr = case Size of
        default -> "";
        _ -> ":" ++ render_exp(Size, Indent)
    end,
    TsStr = case TypeSpecifiers of
        default -> "";
        _ -> "/" ++ string:join([render_type_specifier(T) || T <- TypeSpecifiers], "-")
    end,
    ValStr ++ SizeStr ++ TsStr.

-spec render_type_specifier(atom() | {atom(), integer()}) -> string().
render_type_specifier({unit, N}) -> "unit:" ++ integer_to_list(N);
render_type_specifier(T) when is_atom(T) -> atom_to_list(T).

-spec render_map_assoc(ast:map_assoc() | ast:map_assoc_opt() | ast:map_assoc_req(), non_neg_integer()) -> string().
render_map_assoc({map_field_opt, _, K, V}, Indent) ->
    render_exp(K, Indent) ++ " => " ++ render_exp(V, Indent);
render_map_assoc({map_field_req, _, K, V}, Indent) ->
    render_exp(K, Indent) ++ " := " ++ render_exp(V, Indent).

-spec render_qualifier(ast:qualifier(), non_neg_integer()) -> string().
render_qualifier({generate, _, Pat, E}, Indent) ->
    render_exp(Pat, Indent) ++ " <- " ++ render_exp(E, Indent);
render_qualifier({generate_strict, _, Pat, E}, Indent) ->
    render_exp(Pat, Indent) ++ " <:- " ++ render_exp(E, Indent);
render_qualifier({b_generate, _, Pat, E}, Indent) ->
    render_exp(Pat, Indent) ++ " <= " ++ render_exp(E, Indent);
render_qualifier({m_generate, _, KeyPat, ValPat, E}, Indent) ->
    render_exp(KeyPat, Indent) ++ " := " ++ render_exp(ValPat, Indent) ++ " <- " ++ render_exp(E, Indent);
render_qualifier({m_generate_strict, _, KeyPat, ValPat, E}, Indent) ->
    render_exp(KeyPat, Indent) ++ " := " ++ render_exp(ValPat, Indent) ++ " <:- " ++ render_exp(E, Indent);
render_qualifier({zip, _, Gens}, Indent) ->
    string:join([render_qualifier(G, Indent) || G <- Gens], " && ");
render_qualifier(Exp, Indent) ->
    % filter expression
    render_exp(Exp, Indent).

-spec render_record_field(tuple(), non_neg_integer()) -> string().
render_record_field({record_field, _, Field, Val}, Indent) ->
    atom_to_list(Field) ++ " = " ++ render_exp(Val, Indent);
render_record_field({record_field_other, _, Val}, Indent) ->
    "_ = " ++ render_exp(Val, Indent).
