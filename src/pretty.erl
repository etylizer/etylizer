-module(pretty).

-compile([nowarn_shadow_vars]).
-include_lib("log.hrl").

-export([
         ty/1,
         tyscheme/1,
         constr/1,
         substs/1,
         subst/1,
         constr_block/1,
         loc/1,
         locs/1,
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
         pretty_list/2,
         render_list_with_braces/2,
         ref/1
        ]).

-import(prettypr, [text/1]).

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
                    _ -> beside(NameDoc, text(" <: "), ty(Bound))
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
                _ when is_integer(A) -> integer(A);
                _ -> text([$$, A]) % must be a char
            end;
        {binary, I, J} ->
            text(utils:sformat("<<_:~w, _:_*~w>>", I, J));
        {empty_list} ->
            text("[]");
        {list, U} ->
            beside(text("["), ty(U), text("]"));
        {nonempty_list, U} ->
            beside(text("nonempty_list"), parens(ty(U)));
        {improper_list, U, V} ->
            beside(text("improper_list"), parens(comma(ty(U), ty(V))));
        {nonempty_improper_list, U, V} ->
            beside(text("nonempty_improper_list"), parens(comma(ty(U), ty(V))));
        {fun_simple} ->
            text("fun()");
        {fun_any_arg, U} ->
            beside(text("fun((...) -> "), ty(U), text(")"));
        {fun_full, Args, Res} ->
            beside(text("fun"),
                   parens(beside(
                            parens(comma_sep(lists:map(fun ty/1, Args))),
                            text(" -> "),
                            ty(Res))));
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
        {predef, Name} ->
            beside(atom(Name), text("()"));
        {predef_alias, Name} ->
            beside(atom(Name), text("()"));
        {record, Name, Fields} ->
            FieldsP =
                lists:map(
                  fun({FieldName, U}) ->
                          beside(atom(FieldName), text(" :: "), ty(U))
                  end,
                  Fields),
            beside(text("#" ++ atom_to_list(Name)), brackets(comma_sep(FieldsP)));
        {mu, Var, Ty} ->
            beside(text("mu "), ty(Var), text("."), ty(Ty));
        {named, _Loc, Ref, Args} ->
            RefP =
                case Ref of
                    {ty_ref, _, Name, _} -> atom(Name);
                    {ty_qref, Mod, Name, _} ->
                        beside(atom(Mod), text(":"), atom(Name))
                end,
            beside(RefP, parens(comma_sep(lists:map(fun ty/1, Args))));
        {tuple_any} ->
            text("tuple()");
        {tuple, Args} ->
            brackets(comma_sep(lists:map(fun ty/1, Args)));
        {var, Name} ->
            atom(Name);
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

-spec arity(atom(), ast:arity()) -> doc.
arity(Name, Arity) -> text(utils:sformat("~w/~w", Name, Arity)).

-spec ref(ast:any_ref()) -> doc().
ref(AnyRef) ->
    case AnyRef of
        {ref, Name, Arity} -> arity(Name, Arity);
        {qref, Mod, Name, Arity} ->
            text(utils:sformat("~w:~w/~w", Mod, Name, Arity));
        {local_ref, {Name, Tok}} ->
            beside(atom(Name), text("@"), text(utils:sformat("~w", Tok)))
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
    braces(
      comma_sep(
        lists:map(
          fun({ccase_branch, Locs, Payload}) ->
                {GuardEnv, GuardCs} = constr:case_branch_guard(Payload),
                {BodyEnv, BodyCs} = constr:case_branch_body(Payload),
                ResultCs = constr:case_branch_result(Payload),
                BodyCondCs = constr:case_branch_bodyCond(Payload),
                PrettyBodyCond =
                    case BodyCondCs of
                        none -> text("none");
                        X -> constr(X)
                    end,
                brackets(comma_sep([locs(Locs),
                    kv("guardEnv", constr_env(GuardEnv)),
                    kv("guardCs", constr(GuardCs)),
                    kv("bodyEnv", constr_env(BodyEnv)),
                    kv("bodyCs", constr(BodyCs)),
                    kv("bodyCond", PrettyBodyCond),
                    kv("resultCs", constr(ResultCs))]))
          end,
          L))).

-spec sconstr_bodies([constr:simp_constr_case_branch()]) -> doc().
sconstr_bodies(L) ->
    braces(
      comma_sep(
        lists:map(
          fun({sccase_branch, {GuardsLoc, Guards}, Cond, {BodyLoc, Body}, {ResultLoc, Result}}) ->
                PrettyCond =
                    case Cond of
                        none -> [text("none")];
                        {L2, X} -> [kv("condLoc", loc(L2)), kv("cond", constr(X))]
                    end,
                brackets(comma_sep([
                    kv("guardLoc", loc(GuardsLoc)),
                    kv("guard", constr(Guards))] ++ PrettyCond ++ [
                    kv("bodyLoc", loc(BodyLoc)),
                    kv("body", constr(Body)),
                    kv("resultLoc", loc(ResultLoc)),
                    kv("result", constr(Result))
                    ]))
          end,
          L))).

-spec kv(string(), doc()) -> doc().
kv(K, V) -> beside(text(K), text(":"), V).

-type all_constrs() :: constr:simp_constr() | constr:constr()
                     | sets:set(all_constrs()) | list(all_constrs()).

-spec constr(all_constrs()) -> doc().
constr(X) ->
   case {sets:is_set(X), is_list(X)} of
       {true, _} ->
           braces(comma_sep(lists:map(fun constr/1, sets:to_list(X))));
       {false, true} ->
           brackets(comma_sep(lists:map(fun constr/1, X)));
       {false, false} ->
           case X of
               {csubty, Locs, T1, T2} ->
                   brackets(comma_sep([text("csubty"),
                                       locs(Locs),
                                       ty(T1),
                                       ty(T2)]));
               {scsubty, Loc, T1, T2} ->
                   brackets(comma_sep([text("scsubty"),
                                       loc(Loc),
                                       ty(T1),
                                       ty(T2)]));
               {cvar, Locs, Ref, T} ->
                   brackets(comma_sep([text("cvar"),
                                       locs(Locs),
                                       ref(Ref),
                                       ty(T)]));
               {cop, Locs, Name, Arity, T} ->
                   brackets(comma_sep([text("cop"),
                                       locs(Locs),
                                       beside(atom(Name), text("/"), text(integer_to_list(Arity))),
                                       ty(T)]));
               {cdef, Locs, Env, Cs} ->
                   brackets(comma_sep([text("cdef"),
                                       locs(Locs),
                                       constr_env(Env),
                                       constr(Cs)]));
               {ccase, Locs, CsScrut, CsExhaust, Bodies} ->
                   brackets(comma_sep([text("ccase"),
                                       locs(Locs),
                                       kv("scrutiny", constr(CsScrut)),
                                       kv("exhaust", constr(CsExhaust)),
                                       constr_bodies(Bodies)]));
               {sccase, {LocScrut, CsScrut}, {LocExhaust, CsExhaust}, Bodies} ->
                   brackets(comma_sep([text("sccase"),
                                       kv("scrutinyLoc", loc(LocScrut)),
                                       kv("scrutiny", constr(CsScrut)),
                                       kv("exhaustLoc", loc(LocExhaust)),
                                       kv("exhaust", constr(CsExhaust)),
                                       sconstr_bodies(Bodies)]))
           end
   end.

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

-spec render_list_with_braces(fun((T) -> doc()), list(T)) -> string().
render_list_with_braces(Fun, L) ->
    render(braces(comma_sep(lists:map(Fun, L)))).

