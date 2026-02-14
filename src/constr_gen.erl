-module(constr_gen).

-include("log.hrl").

-export([
         gen_constrs_fun_group/4, gen_constrs_annotated_fun/5,
         sanity_check/2
        ]).

-ifdef(TEST).
-export([
         pat_guard_lower_upper/4,
         ty_of_pat/4
        ]).
-endif.

-compile([nowarn_shadow_vars]).

-record(ctx,
        { var_counter :: counters:counters_ref(),
          symtab :: symtab:t(),
          exhaustiveness_mode :: feature_flags:exhaustiveness_mode(),
          % functions where exhaustiveness is disabled at the constraint generation level
          disable_exhaustiveness = sets:new() :: sets:set({atom(), arity()})
        }).
-type ctx() :: #ctx{}.

-spec new_ctx(symtab:t(), feature_flags:exhaustiveness_mode(), sets:set({atom(), arity()})) -> ctx().
new_ctx(Symtab, ExhaustivenessMode, DisableExhaustiveness) ->
    Counter = counters:new(2, []),
    Ctx = #ctx{ var_counter = Counter, symtab = Symtab, exhaustiveness_mode = ExhaustivenessMode,
                disable_exhaustiveness = DisableExhaustiveness },
    Ctx.

-spec fresh_ty_varname(ctx()) -> ast:ty_varname().
fresh_ty_varname(Ctx) ->
    I = counters:get(Ctx#ctx.var_counter, 1),
    counters:add(Ctx#ctx.var_counter, 1, 1),
    S = utils:sformat("$~w", I),
    list_to_atom(S).

-spec fresh_tyvar(ctx()) -> ast:ty_var().
fresh_tyvar(Ctx) ->
    Alpha = fresh_ty_varname(Ctx),
    {var, Alpha}.

-spec fresh_vars(ctx(), arity()) -> [ast:local_varname()].
fresh_vars(Ctx, N) ->
    I = counters:get(Ctx#ctx.var_counter, 2),
    counters:add(Ctx#ctx.var_counter, 2, 1),
    Loop =
        fun Loop(J) ->
                if
                    J > N -> [];
                    true ->
                        ArgJ = list_to_atom(utils:sformat("$A~w", J)),
                        X = {ArgJ, I},
                        [X | Loop(J + 1)]
                end
        end,
    Loop(1).

-spec mk_locs(string(), ast:loc()) -> constr:locs().
mk_locs(Label, X) -> {Label, utils:single(X)}.

% Inference for a group of mutually recursive functions without type annotations.
-spec gen_constrs_fun_group(feature_flags:exhaustiveness_mode(), symtab:t(), sets:set({atom(), arity()}), [ast:fun_decl()]) -> {constr:constrs(), constr:constr_env()}.
gen_constrs_fun_group(ExhaustivenessMode, Symtab, DisableExhaustiveness, Decls) ->
    lists:foldl(
      fun({function, L, Name, Arity, FunClauses}, {Cs, Env}) ->
              Ctx = new_ctx(Symtab, is_exhaustiveness_disabled_for_fun(Name, Arity, ExhaustivenessMode, DisableExhaustiveness), DisableExhaustiveness),
              Exp = {'fun', L, no_name, FunClauses},
              Alpha = fresh_tyvar(Ctx),
              {ThisCs, _ThisEnv} = exp_constrs(Ctx, Exp, Alpha),
              Ref = {ref, Name, Arity},
              {sets:union(ThisCs, Cs), maps:put(Ref, Alpha, Env)}
      end, {sets:new([{version, 2}]), #{}}, Decls).

% Checking the type spec of a function.
% This function is invoked for each branch of the intersection type in the type spec.
% The idea is that we can give better error messages by pointing out which part of the
% intersection did not type check.
-spec gen_constrs_annotated_fun(feature_flags:exhaustiveness_mode(), symtab:t(), sets:set({atom(), arity()}), ast:ty_full_fun(), ast:fun_decl()) -> constr:constrs().
gen_constrs_annotated_fun(ExhaustivenessMode, Symtab, DisableExhaustiveness, {fun_full, ArgTys, ResTy}, {function, L, Name, Arity, FunClauses}) ->
    Ctx = new_ctx(Symtab, is_exhaustiveness_disabled_for_fun(Name, Arity, ExhaustivenessMode, DisableExhaustiveness), DisableExhaustiveness),
    {Args, Body} = fun_clauses_to_exp(Ctx, L, FunClauses),
    if length(Args) =/= length(ArgTys) orelse length(Args) =/= Arity ->
            errors:ty_error(L, "Arity mismatch for function ~w", Name);
       true -> ok
    end,
    ArgRefs = lists:map(fun(V) -> {local_ref, V} end, Args),
    Env = maps:from_list(lists:zip(ArgRefs, ArgTys)),
    {BodyCs, _BodyEnv} = exps_constrs(Ctx, L, Body, ResTy),
    Msg = utils:sformat("definition of ~w/~w", Name, Arity),
    utils:single({cdef, mk_locs(Msg, L), Env, BodyCs}).

% Returns variables bound in all branches with the union of their types
-spec safe_env_from_branch_envs([constr:constr_env()]) -> constr:constr_env().
safe_env_from_branch_envs(BodyEnvs) ->
    case BodyEnvs of
        [] -> #{};
        [FirstEnv | RestEnvs] ->
            FirstVars = sets:from_list(maps:keys(FirstEnv), [{version, 2}]),
            CommonVars = lists:foldl(
                fun(BranchEnv, Acc) ->
                    BranchVars = sets:from_list(maps:keys(BranchEnv), [{version, 2}]),
                    sets:intersection(Acc, BranchVars)
                end,
                FirstVars,
                RestEnvs),
            sets:fold(
                fun(Var, Acc) ->
                    Tys = lists:map(fun(BranchEnv) -> maps:get(Var, BranchEnv) end, BodyEnvs),
                    maps:put(Var, ast_lib:mk_union(Tys), Acc)
                end,
                #{},
                CommonVars)
    end.

% constraints for a sequence of expressions building up safe environment in forward order
-spec exps_constrs(ctx(), ast:loc(), [ast:exp()], ast:ty()) -> {constr:constrs(), constr:constr_env()}.
exps_constrs(_Ctx, _L, [], _T) ->
    ?ABORT("empty list of expressions");
exps_constrs(Ctx, _L, [E], T) ->
    exp_constrs(Ctx, E, T);
exps_constrs(Ctx, L, [E | Rest], T) ->
    Alpha = fresh_tyvar(Ctx),
    {Cs, Env} = exp_constrs(Ctx, E, Alpha),
    {RestCs, RestEnv} = exps_constrs(Ctx, L, Rest, T),
    case maps:size(Env) of % don't need to wrap anything if it's empty
        0 -> {sets:union(Cs, RestCs), RestEnv};
        _ -> {sets:union(Cs, sets:from_list([{cdef, mk_locs("safe vars", L), Env, RestCs}])), maps:merge(Env, RestEnv)}
    end.

% Like exp_constrs, but returns the TYPE of the expression directly instead of
% constraining it against a target T. For simple expressions (variables, literals),
% this avoids creating an intermediate fresh type variable. Falls back to creating
% a fresh variable for complex expressions.
-spec exp_constrs_tyof(ctx(), ast:exp()) -> {ast:ty(), constr:constrs(), constr:constr_env()}.
exp_constrs_tyof(Ctx, E) ->
    case E of
        {'atom', _L, A} -> {{singleton, A}, sets:new([{version, 2}]), #{}};
        {'char', _L, C} -> {{singleton, C}, sets:new([{version, 2}]), #{}};
        {'integer', _L, I} -> {{singleton, I}, sets:new([{version, 2}]), #{}};
        {'float', _L, _F} -> {{predef, float}, sets:new([{version, 2}]), #{}};
        {var, L, AnyRef} ->
            AlphaName = fresh_ty_varname(Ctx),
            Msg = utils:sformat("var ~s", pretty:render(pretty:ref(AnyRef))),
            Locs = mk_locs(Msg, L),
            Mater = {cvarmater, Locs, AnyRef, AlphaName},
            {{var, AlphaName}, utils:single(Mater), #{}};
        _ ->
            Alpha = fresh_tyvar(Ctx),
            {Cs, Env} = exp_constrs(Ctx, E, Alpha),
            {Alpha, Cs, Env}
    end.

-spec exp_constrs(ctx(), ast:exp(), ast:ty()) -> {constr:constrs(), constr:constr_env()}.
exp_constrs(Ctx, E, T) ->
    case E of
        {'atom', L, A} -> {utils:single({csubty, mk_locs("atom literal", L), {singleton, A}, T}), #{}};
        {'char', L, C} -> {utils:single({csubty, mk_locs("char literal", L), {singleton, C}, T}), #{}};
        {'integer', L, I} -> {utils:single({csubty, mk_locs("int literal", L), {singleton, I}, T}), #{}};
        {'float', L, _F} -> {utils:single({csubty, mk_locs("float literal", L), {predef, float}, T}), #{}};
        {'string', L, ""} -> {utils:single({csubty, mk_locs("empty string literal", L), {empty_list}, T}), #{}};
        {'string', L, _S} -> {utils:single({csubty, mk_locs("string literal", L), {predef_alias, nonempty_string}, T}), #{}};
        {bin, L, []} -> {utils:single({csubty, mk_locs("empty bitstring", L), {bitstring, 0, 0}, T}), #{}};
        {bin, L, BinElems} ->
            {ElemCs, ResultTy} = bin_expr_constrs(Ctx, L, BinElems),
            {sets:add_element({csubty, mk_locs("bitstring", L), ResultTy, T}, ElemCs), #{}};
        {bc, L, Exp, Qs} ->
            {Env, Cs0} = process_qualifiers(Ctx, L, Qs, #{}, sets:new()),
            Beta = fresh_tyvar(Ctx),
            {ExpCs, _ExpEnv} = exp_constrs(Ctx, Exp, Beta),
            BodyCs = sets:from_list([{cdef, mk_locs("binary comprehension body", L), Env, ExpCs}], []),
            ResultTy = {bitstring, 0, 8},  % binary() result
            Cs1 = sets:add_element({csubty, mk_locs("binary comprehension result", L), ResultTy, T}, BodyCs),
            {sets:union(Cs0, Cs1), #{}};
        {block, L, Es} ->
            exps_constrs(Ctx, L, Es, T);
        {'case', L, ScrutE, Clauses} ->
            Alpha = fresh_tyvar(Ctx),
            {Cs0, ScrutEnv} = scrut_constrs_compact(Ctx, ScrutE, Alpha),
            NeedsUnmatchedCheck = needs_unmatched_check(Clauses),
            {BodyList, Lowers, _Uppers, CsCases, BodyEnvs} =
                lists:foldl(fun (Clause = {case_clause, LocClause, _, _, _},
                                 {BodyList, Lowers, Uppers, AccCs, AccEnvs}) ->
                                    ?LOG_TRACE("Generating constraint for case clause at ~s: Lowers=~s, Uppers=~s",
                                               ast:format_loc(LocClause),
                                               pretty:render_tys(Lowers),
                                               pretty:render_tys(Uppers)),
                                    {ThisLower, ThisUpper, ThisCs, ThisConstrBody, ThisBodyEnv} =
                                        case_clause_constrs(
                                          Ctx,
                                          ty_without(Alpha, ast_lib:mk_union(Lowers)),
                                          ScrutE,
                                          ScrutEnv,
                                          NeedsUnmatchedCheck,
                                          Lowers,
                                          Clause,
                                          T),
                                    {BodyList ++ [ThisConstrBody],
                                     Lowers ++ [ThisLower],
                                     Uppers ++ [ThisUpper],
                                     sets:union(ThisCs, AccCs),
                                     AccEnvs ++ [ThisBodyEnv]}
                            end,
                            {[], [], [], sets:new([{version, 2}]), []},
                            Clauses),
            CsScrut = sets:union(Cs0, CsCases),
            HasBinPat = lists:any(fun({case_clause, _, Pat, _, _}) -> has_bin_pat(Pat) end, Clauses),
            Exhaust =
            case {Ctx#ctx.exhaustiveness_mode, HasBinPat} of
                {enabled, false} -> utils:single(
                              {csubty, mk_locs("case exhaustiveness", L), Alpha, ast_lib:mk_union(Lowers)});
                _ -> sets:new()
            end,
            SafeEnv = intersect_envs(ScrutEnv, safe_env_from_branch_envs(BodyEnvs)),
            {sets:from_list([
                {ccase, mk_locs("case", L), CsScrut, Exhaust, BodyList}
            ], [{version, 2}]), SafeEnv};
        {'catch', L, CatchE} ->
            Top = {predef, any},
            {Cs, _CatchEnv} = exp_constrs(Ctx, CatchE, Top),
            {sets:add_element({csubty, mk_locs("result of catch", L), Top, T}, Cs), #{}};
        {'try', L, Body, [], CatchClauses, AfterBody} ->
            % 'of clauses' are always [] after AST transformation.

            % discard env, no variable is safe after env
            TryResultTy = fresh_tyvar(Ctx),
            {TryBodyCs, _TryBodyEnv} = exps_constrs(Ctx, L, Body, TryResultTy),

            % Process catch clauses
            {CatchBodyList, CatchCs} =
                case CatchClauses of
                    [] -> {[], sets:new()};
                    _ ->
                        {CBList, CCs} =
                            lists:foldl(
                                fun(CatchClause, {AccBodyList, AccCs}) ->
                                    {ThisCs, ThisBody, _ThisEnv} =
                                        catch_clause_constrs(Ctx, CatchClause, T),
                                    {AccBodyList ++ [ThisBody],
                                     sets:union(ThisCs, AccCs)}
                                end,
                                {[], sets:new()},
                                CatchClauses),
                        {CBList, CCs}
                end,

            % after section, result is discarded
            AfterCs = case AfterBody of
                [] -> sets:new();
                _ ->
                    AfterTy = fresh_tyvar(Ctx),
                    {ACs, _AfterEnv} = exps_constrs(Ctx, L, AfterBody, AfterTy),
                    ACs
            end,

            % Try body result is one branch, catch clauses are other branches
            % Try body is a branch that always succeeds (no guard)
            TryResCs = utils:single({csubty, mk_locs("try body result", L), TryResultTy, T}),
            TryBodyPayload = constr:mk_case_branch_payload(
                {#{}, sets:new()},         % Guard (always true, no env)
                {#{}, TryBodyCs},          % Body constraints
                none,                      % No redundancy check
                TryResCs),                 % Result constraint
            TryBodyBranch = {ccase_branch, mk_locs("try body", L), TryBodyPayload},
            AllBodyList = [TryBodyBranch | CatchBodyList],

            AllCs = sets:union([TryBodyCs, CatchCs, AfterCs]),

            % Result: create the ccase constraint
            % Note: TryBodyEnv should NOT be wrapped around the ccase because:
            % 1. exps_constrs already embeds the environment in TryBodyCs via internal cdef
            % 2. Wrapping would make try body vars visible to catch clauses (wrong!)
            % 3. Per Erlang rules, try body vars are unsafe in catch/after sections
            ResultCs = sets:from_list([{ccase, mk_locs("try-catch", L), AllCs,
                                       sets:new(), AllBodyList}]),

            {ResultCs, #{}};
        {cons, L, Head, Tail} ->
            Alpha = fresh_tyvar(Ctx),
            {C1, _Env1} = exp_constrs(Ctx, Head, Alpha),
            Beta = fresh_tyvar(Ctx),
            {C2, _Env2} = exp_constrs(Ctx, Tail, Beta),
            Cs = sets:union(C1, C2),
            ListC = {csubty, mk_locs("cons constructor", L), {cons, Alpha, Beta}, T},
            {sets:add_element(ListC, Cs), #{}};
        {fun_ref, L, GlobalRef} ->
            {utils:single({cvar, mk_locs("function ref", L), GlobalRef, T}), #{}};
        {'fun', L, RecName, FunClauses} ->
            {Args, BodyExps} = fun_clauses_to_exp(Ctx, L, FunClauses),
            ArgTys = lists:map(fun(X) -> {{local_ref, X}, fresh_tyvar(Ctx)} end, Args),
            ArgEnv = maps:from_list(ArgTys),
            ResTy = fresh_tyvar(Ctx),
            FunTy = {fun_full, lists:map(fun({_, Ty}) -> Ty end, ArgTys), ResTy},
            {CsBody, _BodySafeEnv} = exps_constrs(Ctx, L, BodyExps, ResTy),
            BodyEnv =
                case RecName of
                    no_name -> ArgEnv;
                    {local_bind, F} -> maps:put({local_ref, F}, FunTy, ArgEnv)
                end,
            {sets:from_list([{cdef, mk_locs("function def", L), BodyEnv, CsBody},
                            {csubty, mk_locs("result of fun exp", L), FunTy, T}], [{version, 2}]), #{}};
        {call, L, Var = {var, _, _}, Args} ->
            {var_funcall_constrs(Ctx, L, Var, Args, T), #{}};
        {call, L, FunExp, Args} ->
            {gen_funcall_constrs(Ctx, L, FunExp, Args, T), #{}};
        {call_remote, L, ModExp, FunExp, Args} ->
            {dyncall_constrs(Ctx, L, ModExp, FunExp, Args, T), #{}};
        ({'if', _, _} = IfExp) ->
            exp_constrs(Ctx, if_exp_to_case_exp(IfExp), T);
        {lc, L, Exp, Qs} ->
            {Env, Cs0} = process_qualifiers(Ctx, L, Qs, #{}, sets:new()),
            Beta = fresh_tyvar(Ctx), % element result
            % generate constraints for body expression in qualifier environment
            {ExpCs, _ExpEnv} = exps_constrs(Ctx, L, [Exp], Beta),
            BodyCs = sets:from_list([{cdef, mk_locs("list comprehension body", L), Env, ExpCs}], []),
            % comprehension result is list of body type
            ListTy = stdtypes:tlist(Beta),
            Cs1 = sets:add_element({csubty, mk_locs("list comprehension result", L), ListTy, T}, BodyCs),
            {sets:union(Cs0, Cs1), #{}};
        {mc, L, K, V, Qs} ->
            {Env, Cs0} = process_qualifiers(Ctx, L, Qs, #{}, sets:new()),

            % key and value types
            KeyAlpha = fresh_tyvar(Ctx),
            ValAlpha = fresh_tyvar(Ctx),
            {KeyCs, _KeyEnv} = exps_constrs(Ctx, L, [K], KeyAlpha),
            {ValCs, _ValEnv} = exps_constrs(Ctx, L, [V], ValAlpha),

            BodyCs = sets:from_list([
                {cdef, mk_locs("map comprehension key", L), Env, KeyCs},
                {cdef, mk_locs("map comprehension value", L), Env, ValCs}
            ], []),

            % comprehension result is map of key/value types
            MapTy = stdtypes:tmap(KeyAlpha, ValAlpha),
            Cs1 = sets:add_element(
                {csubty, mk_locs("map comprehension result", L), MapTy, T},
                BodyCs
            ),
            {sets:union(Cs0, Cs1), #{}};
        {map_create, L, []} ->
            {utils:single({csubty, mk_locs("empty map", L), {map, []}, T}), #{}};
        {map_create, L, Assocs} ->
            KeyAlpha = fresh_tyvar(Ctx),
            ValAlpha = fresh_tyvar(Ctx),
            MapTy = {map, [{map_field_opt, KeyAlpha, ValAlpha}]},
            AssocsCs =
                lists:foldl(
                  fun({map_field_opt, _FieldL, KeyE, ValE}, AccCs) ->
                          {KeyCs, _KeyEnv} = exp_constrs(Ctx, KeyE, KeyAlpha),
                          {ValCs, _ValEnv} = exp_constrs(Ctx, ValE, ValAlpha),
                          sets:union([AccCs, KeyCs, ValCs])
                  end,
                  sets:new([{version, 2}]),
                  Assocs),
            ResultC = {csubty, mk_locs("map_create", L), MapTy, T},
            {sets:add_element(ResultC, AssocsCs), #{}};
        {map_update, L, MapExp, Assocs} ->
            KeyAlpha = fresh_tyvar(Ctx),
            ValAlpha = fresh_tyvar(Ctx),
            MapTy = {map, [{map_field_opt, KeyAlpha, ValAlpha}]},
            {Cs1, _MapEnv} = exp_constrs(Ctx, MapExp, MapTy),
            Cs2 =
                lists:foldl(
                fun(Assoc, AccCs) ->
                    {KeyE, ValE} =
                        case Assoc of
                            {map_field_opt, _FieldL, K, V} -> {K, V};
                            {map_field_req, _FieldL, K, V} -> {K, V}
                        end,
                    {KeyCs, _KeyEnv} = exp_constrs(Ctx, KeyE, KeyAlpha),
                    {ValCs, _ValEnv} = exp_constrs(Ctx, ValE, ValAlpha),
                    sets:union([AccCs, KeyCs, ValCs])
                end,
                Cs1,
                Assocs),
            ResultC = {csubty, mk_locs("map_update", L), MapTy, T},
            {sets:add_element(ResultC, Cs2), #{}};
        {nil, L} ->
            {utils:single({csubty, mk_locs("result of nil", L), {empty_list}, T}), #{}};
        {op, L, Op, Lhs, Rhs} ->
            {Alpha1, Cs1, Env1} = exp_constrs_tyof(Ctx, Lhs),
            {Alpha2, Cs2, Env2} = exp_constrs_tyof(Ctx, Rhs),
            Beta = fresh_tyvar(Ctx),
            MsgTy = utils:sformat("type of op ~w", Op),
            MsgRes = utils:sformat("result of op ~w", Op),
            OpCs = sets:from_list(
                     [{cop, mk_locs(MsgTy, L), Op, 2, {fun_full, [Alpha1, Alpha2], Beta}},
                      {csubty, mk_locs(MsgRes, L), Beta, T}], [{version, 2}]),
            % If LHS binds variables, make them available to RHS
            Cs2WithEnv = case maps:size(Env1) of
                0 -> Cs2;
                _ -> sets:from_list([{cdef, mk_locs("op lhs vars", L), Env1, Cs2}])
            end,
            % Variables from both sides may be visible after the operator
            CombinedEnv = intersect_envs(Env1, Env2),
            {sets:union([Cs1, Cs2WithEnv, OpCs]), CombinedEnv};
        {op, L, Op, Arg} ->
            {Alpha, ArgCs, ArgEnv} = exp_constrs_tyof(Ctx, Arg),
            Beta = fresh_tyvar(Ctx),
            MsgTy = utils:sformat("type of op ~w", Op),
            MsgRes = utils:sformat("result of op ~w", Op),
            OpCs = sets:from_list(
                     [{cop, mk_locs(MsgTy, L), Op, 1, {fun_full, [Alpha], Beta}},
                      {csubty, mk_locs(MsgRes, L), Beta, T}], [{version, 2}]),
            {sets:union(ArgCs, OpCs), ArgEnv};
        {'receive', L, CaseClauses} ->
            receive_constrs(Ctx, L, CaseClauses, T);
        {receive_after, L, CaseClauses, TimeoutExp, AfterBody} ->
            receive_after_constrs(Ctx, L, CaseClauses, TimeoutExp, AfterBody, T);
        {record_create, L, Name, GivenFields} ->
            {_, DefFields} = symtab:lookup_record(Name, L, Ctx#ctx.symtab),
            VarFields =
                lists:map(
                    fun ({N, _}) ->
                        Alpha = fresh_tyvar(Ctx),
                        {N, Alpha}
                    end,
                    DefFields),
            DefFieldNames = sets:from_list(lists:map(fun ({N, _}) -> N end, DefFields), [{version, 2}]),
            GivenFieldNames =
                % FIXME: deal with record_field_other, which assigns a value to all fields
                % not mentioned explicitly
                sets:from_list(lists:map(fun ({record_field, _L, N, _Exp}) -> N end, GivenFields), [{version, 2}]),
            case sets:is_subset(GivenFieldNames, DefFieldNames) of
                false -> errors:ty_error(L, "too many record fields given", []);
                true ->
                    case sets:is_subset(DefFieldNames, GivenFieldNames) of
                        true -> ok;
                        false -> errors:ty_error(L, "not all record fields given", [])
                    end
            end,
            Cs =
                lists:foldr(
                    fun({record_field, _L, N, Exp}, Cs) ->
                        {ok, Ty} = utils:assocs_find(N, VarFields), % we checked before that all fields are present
                        {ThisCs, _ThisEnv} = exp_constrs(Ctx, Exp, Ty),
                        sets:union(Cs, ThisCs)
                    end,
                    sets:new([{version, 2}]),
                    GivenFields),
            RecTupleTy = records:encode_record_ty({Name, VarFields}),
            RecConstr = {csubty, mk_locs("record value constructor", L), RecTupleTy, T},
            {sets:add_element(RecConstr, Cs), #{}};
        {record_field, L, Exp, RecName, FieldName} ->
            {_, DefFields} = symtab:lookup_record(RecName, L, Ctx#ctx.symtab),
            Alpha = fresh_tyvar(Ctx),
            VarFields =
                lists:map(
                    fun ({N, _}) ->
                        Ty =
                            case N =:= FieldName of
                                true -> Alpha;
                                false -> stdtypes:tany()
                            end,
                        {N, Ty}
                    end,
                    DefFields),
            RecTupleTy = records:encode_record_ty({RecName, VarFields}),
            {Cs, _ExpEnv} = exp_constrs(Ctx, Exp, RecTupleTy),
            FieldConstr = {csubty, mk_locs("record field access", L), Alpha, T},
            {sets:add_element(FieldConstr, Cs), #{}};
        {record_index, L, RecName, FieldName} ->
            RecTy = symtab:lookup_record(RecName, L, Ctx#ctx.symtab),
            {_FieldTy, Idx} = records:lookup_field_index(RecTy, FieldName, L),
            Constr = {csubty, mk_locs("record field index", L), stdtypes:tint(Idx + 1), T},
            {utils:single(Constr), #{}};
        {record_update, L, Exp, RecName, FieldUpdates} ->
            {_, DefFields} = symtab:lookup_record(RecName, L, Ctx#ctx.symtab),
            UpdatedFieldNames =
                sets:from_list(
                    lists:map(fun({record_field, _, FieldName, _}) -> FieldName end, FieldUpdates)
                    , [{version, 2}]),
            % For typechecking the expression Exp, the updated fields can have type any().
            % But all fields F not updated must be of type Alpha_F (a type variable)
            % The values for all updated fields G must have type Alpha_G
            % The resulting record type then combines the Alpha_F and Alpha_G
            % A list of tuples {name of field, expected type in exp, type in result}
            FieldTypes =
                lists:map(
                    fun ({N, _}) ->
                        {TyExp, TyRes} =
                            case sets:is_element(N, UpdatedFieldNames) of
                                true -> {stdtypes:tany(), fresh_tyvar(Ctx)};
                                false ->
                                    Alpha = fresh_tyvar(Ctx),
                                    {Alpha, Alpha}
                            end,
                        {N, TyExp, TyRes}
                    end,
                    DefFields),
            FieldsForExp = lists:map(fun ({N, Ty, _}) -> {N, Ty} end, FieldTypes),
            RecTupleTyExp = records:encode_record_ty({RecName, FieldsForExp}),
            {ExpCs, _ExpEnv} = exp_constrs(Ctx, Exp, RecTupleTyExp),
            FieldsForRes = lists:map(fun ({N, _, Ty}) -> {N, Ty} end, FieldTypes),
            RecTyRes = {RecName, FieldsForRes},
            RecTupleTyRes = records:encode_record_ty(RecTyRes),
            ResConstr = {csubty, mk_locs("record result", L), RecTupleTyRes, T},
            {lists:foldr(
                fun({record_field, FieldUpdateLoc, FieldName, FieldExp}, Cs) ->
                    FieldTy = records:lookup_field_ty(RecTyRes, FieldName, FieldUpdateLoc),
                    {ThisCs, _ThisEnv} = exp_constrs(Ctx, FieldExp, FieldTy),
                    sets:union(Cs, ThisCs)
                end,
                sets:add_element(ResConstr, ExpCs),
                FieldUpdates), #{}};
        {tuple, L, Args} ->
            {Tys, Cs} =
                lists:foldr(
                  fun(Arg, {Tys, Cs}) ->
                          {ArgTy, ThisCs, _ThisEnv} = exp_constrs_tyof(Ctx, Arg),
                          {[ArgTy | Tys], sets:union(Cs, ThisCs)}
                  end,
                  {[], sets:new([{version, 2}])},
                  Args),
            TupleC = {csubty, mk_locs("tuple constructor", L), {tuple, Tys}, T},
            {sets:add_element(TupleC, Cs), #{}};
        {var, L, AnyRef} ->
            Msg = utils:sformat("var ~s", pretty:render(pretty:ref(AnyRef))),
            AlphaName = fresh_ty_varname(Ctx),
            Locs = mk_locs(Msg, L),
            Mater = {cvarmater, Locs, AnyRef, AlphaName},
            Link = {csubty, Locs, {var, AlphaName}, T},
            {sets:from_list([Mater, Link]), #{}};
        {assert, Loc, Exp, TargetType} ->
            % Γ ⊢ e : alpha   TargetType <: alpha   TargetType <: T
            % --------------------------------------- constr-downcast
            % Γ ⊢ (e ::: TargetType) : T
            Alpha = fresh_tyvar(Ctx), 
            {Cons, Env} = exp_constrs(Ctx, Exp, Alpha),
            DowncastConstr = {csubty, mk_locs("downcast", Loc), TargetType, Alpha},
            SubsumConstr = {csubty, mk_locs("downcast result", Loc), TargetType, T},
            {sets:add_element(SubsumConstr, sets:add_element(DowncastConstr, Cons)), Env};
        {annotate, L, Exp, Type} ->
            % Γ ⊢ e : τ   τ <: T
            % ------------------- constr-annot
            % Γ ⊢ (e :: τ) : T
            {Cons, Env} = exp_constrs(Ctx, Exp, Type),
            Annot = {csubty, mk_locs("type annotation", L), Type, T},
            {sets:add_element(Annot, Cons), Env};
        X -> errors:uncovered_case(?FILE, ?LINE, X)
    end.


% Analyze a bitstring type specifier list to determine segment type, signedness, default size, and unit.
-spec analyze_bin_tyspec(default | ast:bitstring_tyspec_list()) ->
    {integer | float | binary | bitstring | utf8 | utf16 | utf32, boolean(), integer() | default, integer()}.
analyze_bin_tyspec(default) -> {integer, false, 8, 1};
analyze_bin_tyspec(TyspecList) ->
    Type = determine_segment_type(TyspecList),
    Signed = lists:member(signed, TyspecList),
    Unit = case lists:keyfind(unit, 1, TyspecList) of
        {unit, U} -> U;
        false -> default_unit(Type)
    end,
    DefaultSize = default_size(Type),
    {Type, Signed, DefaultSize, Unit}.

-spec determine_segment_type(ast:bitstring_tyspec_list()) -> integer | float | binary | bitstring | utf8 | utf16 | utf32.
determine_segment_type([]) -> integer;
determine_segment_type([integer | _]) -> integer;
determine_segment_type([float | _]) -> float;
determine_segment_type([binary | _]) -> binary;
determine_segment_type([bytes | _]) -> binary;
determine_segment_type([bitstring | _]) -> bitstring;
determine_segment_type([bits | _]) -> bitstring;
determine_segment_type([utf8 | _]) -> utf8;
determine_segment_type([utf16 | _]) -> utf16;
determine_segment_type([utf32 | _]) -> utf32;
determine_segment_type([_ | Rest]) -> determine_segment_type(Rest).

-spec default_unit(integer | float | binary | bitstring | utf8 | utf16 | utf32) -> integer().
default_unit(integer) -> 1;
default_unit(float) -> 1;
default_unit(binary) -> 8;
default_unit(bitstring) -> 1;
default_unit(utf8) -> 1;
default_unit(utf16) -> 1;
default_unit(utf32) -> 1.

-spec default_size(integer | float | binary | bitstring | utf8 | utf16 | utf32) -> integer() | default.
default_size(integer) -> 8;
default_size(float) -> 64;
default_size(binary) -> default;
default_size(bitstring) -> default;
default_size(utf8) -> default;
default_size(utf16) -> default;
default_size(utf32) -> default.

% Generate constraints for binary expression elements and compute result type.
-spec bin_expr_constrs(ctx(), ast:loc(), [ast:exp_bitstring_elem()]) -> {constr:constrs(), ast:ty()}.
bin_expr_constrs(Ctx, L, BinElems) ->
    {Cs, TotalBits, AllByteAligned, AllFixed} =
        lists:foldl(
            fun({bin_element, ElemL, Value, Size, TyspecList}, {AccCs, AccBits, AccAligned, AccFixed}) ->
                {SegType, _Signed, DefaultSize, Unit} = analyze_bin_tyspec(TyspecList),
                % Generate constraint for the value expression
                % String literals in binary construction are expanded to bytes;
                % for utf types, strings are also valid values
                IsStringValue = case Value of
                    {'string', _, _} -> true;
                    _ -> false
                end,
                ValueTy = case {SegType, IsStringValue} of
                    {_, true} -> {predef, any};  % strings in binaries are always valid
                    {integer, _} -> {predef, integer};
                    {float, _} -> {predef_alias, number};  % floats accept integers too
                    {binary, _} when Unit =:= 8 -> {bitstring, 0, 8};
                    {binary, _} -> {bitstring};  % binary with non-default unit accepts any bitstring
                    {bitstring, _} -> {bitstring};
                    {utf8, _} -> {predef, integer};
                    {utf16, _} -> {predef, integer};
                    {utf32, _} -> {predef, integer}
                end,
                Alpha = fresh_tyvar(Ctx),
                {ValCs, _ValEnv} = exp_constrs(Ctx, Value, Alpha),
                ValConstr = {csubty, mk_locs("bin element value", ElemL), Alpha, ValueTy},
                % Generate constraint for the size expression (if present)
                SizeCs = case Size of
                    default -> sets:new([{version, 2}]);
                    _ ->
                        SizeAlpha = fresh_tyvar(Ctx),
                        {SCs, _SEnv} = exp_constrs(Ctx, Size, SizeAlpha),
                        sets:add_element(
                            {csubty, mk_locs("bin element size", ElemL), SizeAlpha, {predef, integer}},
                            SCs)
                end,
                % Compute bit contribution and alignment
                % String values contribute length(Str) * DefaultSize * Unit bits
                StrLen = case Value of
                    {'string', _, S} -> length(S);
                    _ -> 0
                end,
                {NewBits, NewAligned, NewFixed} = case {Size, DefaultSize, SegType, IsStringValue} of
                    {default, default, utf8, true} -> {AccBits, AccAligned, false};
                    {default, default, utf16, true} -> {AccBits, AccAligned, false};
                    {default, default, utf32, true} ->
                        Bits = StrLen * 32,
                        {AccBits + Bits, AccAligned, AccFixed};
                    {default, _, _, true} ->
                        % String with integer/default type: each char is DefaultSize*Unit bits
                        DS = case DefaultSize of default -> 8; _ -> DefaultSize end,
                        Bits = StrLen * DS * Unit,
                        {AccBits + Bits, AccAligned andalso (Bits rem 8 =:= 0), AccFixed};
                    {default, default, utf8, _} -> {AccBits, AccAligned, false};
                    {default, default, utf16, _} -> {AccBits, AccAligned, false};
                    {default, default, utf32, _} -> {AccBits + 32, AccAligned, AccFixed};
                    {default, default, binary, _} -> {AccBits, AccAligned, false};
                    {default, default, bitstring, _} -> {AccBits, false, false};
                    {default, DS, _, _} ->
                        Bits = DS * Unit,
                        {AccBits + Bits, AccAligned andalso (Bits rem 8 =:= 0), AccFixed};
                    {{integer, _, V}, _, _, _} when is_integer(V) ->
                        Bits = V * Unit,
                        {AccBits + Bits, AccAligned andalso (Bits rem 8 =:= 0), AccFixed};
                    _ ->
                        % Variable size: can't know bit count
                        {AccBits, AccAligned andalso (Unit rem 8 =:= 0), false}
                end,
                {sets:union([AccCs, ValCs, SizeCs, sets:from_list([ValConstr])]),
                 NewBits, NewAligned, NewFixed}
            end,
            {sets:new([{version, 2}]), 0, true, true},
            BinElems),
    ResultTy = case {AllFixed, AllByteAligned, TotalBits rem 8 =:= 0} of
        {true, true, true} -> {bitstring, TotalBits, 0};
        {true, _, true} -> {bitstring, TotalBits, 0};
        {true, _, false} -> {bitstring, TotalBits, 0};
        {false, true, true} -> {bitstring, TotalBits, 8};
        {false, true, false} -> {bitstring, TotalBits, 8};
        {false, false, _} ->
            ?LOG_WARN("Non-byte-aligned binary expression at ~s, using bitstring()", ast:format_loc(L)),
            {bitstring}
    end,
    {Cs, ResultTy}.

-spec process_qualifiers(ctx(), ast:loc(), [ast:qualifier()], constr:constr_env(), constr:constrs()) ->
          {constr:constr_env(), constr:constrs()}.
process_qualifiers(_Ctx, _Loc, [], Env, Cs) -> {Env, Cs};
process_qualifiers(Ctx, Loc, [Q | Qs], Env, Cs) ->
    case Q of
        % TODO is _ExpEnv for generators just discarded?
        % strict list generator: Pat <:- Exp
        {generate_strict, LGen, Pat, Exp} ->
            Alpha = fresh_tyvar(Ctx),
            {ExpCs, _ExpEnv} = exp_constrs(Ctx, Exp, stdtypes:tlist(Alpha)),

            % For strict generators, the list element type must be a subtype of the pattern type
            TyPat = ty_of_pat(Ctx#ctx.symtab, Env, Pat, upper),
            StrictCs = sets:from_list([
                {csubty, mk_locs("strict list generator", LGen), Alpha, TyPat}
            ]),

            {PatCs, PatEnv} = pat_env(Ctx, LGen, Alpha, Pat),
            NewEnv = intersect_envs(Env, PatEnv),
            process_qualifiers(Ctx, Loc, Qs, NewEnv, sets:union([Cs, ExpCs, PatCs, StrictCs]));
        % list generator: Pat <- Exp
        {generate, LGen, Pat, Exp} ->
            Alpha = fresh_tyvar(Ctx), % list elements 
            Beta = fresh_tyvar(Ctx), % pattern

            {ExpCs, _ExpEnv} = exp_constrs(Ctx, Exp, stdtypes:tlist(Alpha)),

            TyPat = ty_of_pat(Ctx#ctx.symtab, Env, Pat, upper),
            {PatCs, PatEnv} = pat_env(Ctx, LGen, Beta, Pat),

            GeneratorC = [
                          {csubty, mk_locs("pattern lower bound", LGen), ast_lib:mk_intersection([Alpha, TyPat]), Beta},
                          {csubty, mk_locs("pattern upper bound", LGen), Beta, Alpha}
                         ],
            NewEnv = intersect_envs(Env, PatEnv),
            process_qualifiers(Ctx, Loc, Qs, NewEnv, sets:union([Cs, ExpCs, PatCs, sets:from_list(GeneratorC)]));
        {zip, LGen, NestedQualifiers} ->
            {NewEnv, NewCs} = process_qualifiers(Ctx, LGen, NestedQualifiers, Env, Cs),
            process_qualifiers(Ctx, Loc, Qs, NewEnv, NewCs);
        % Pat <= Exp (binary generator)
        {b_generate, LGen, Pat, Exp} ->
            Alpha = fresh_tyvar(Ctx),
            Beta = fresh_tyvar(Ctx),
            {ExpCs, _ExpEnv} = exp_constrs(Ctx, Exp, {bitstring}),
            TyPat = ty_of_pat(Ctx#ctx.symtab, Env, Pat, upper),
            {PatCs, PatEnv} = pat_env(Ctx, LGen, Beta, Pat),
            GeneratorC = [
                {csubty, mk_locs("binary pattern lower bound", LGen), ast_lib:mk_intersection([Alpha, TyPat]), Beta},
                {csubty, mk_locs("binary pattern upper bound", LGen), Beta, Alpha}
            ],
            NewEnv = intersect_envs(Env, PatEnv),
            process_qualifiers(Ctx, Loc, Qs, NewEnv, sets:union([Cs, ExpCs, PatCs, sets:from_list(GeneratorC)]));
        % Pat <:= Exp (strict binary generator)
        {b_generate_strict, LGen, Pat, Exp} ->
            Alpha = fresh_tyvar(Ctx),
            {ExpCs, _ExpEnv} = exp_constrs(Ctx, Exp, {bitstring}),
            TyPat = ty_of_pat(Ctx#ctx.symtab, Env, Pat, upper),
            StrictCs = sets:from_list([
                {csubty, mk_locs("strict binary generator", LGen), Alpha, TyPat}
            ]),
            {PatCs, PatEnv} = pat_env(Ctx, LGen, Alpha, Pat),
            NewEnv = intersect_envs(Env, PatEnv),
            process_qualifiers(Ctx, Loc, Qs, NewEnv, sets:union([Cs, ExpCs, PatCs, StrictCs]));
        % strict map generator: KeyPat := ValPat <:- Exp
        {m_generate_strict, LGen, KeyPat, ValPat, Exp} ->
            KeyAlpha = fresh_tyvar(Ctx),
            ValAlpha = fresh_tyvar(Ctx),
            {ExpCs, _ExpEnv} = exp_constrs(Ctx, Exp, stdtypes:tmap(KeyAlpha, ValAlpha)),

            % For strict generators, the map element types must be subtypes of the pattern types
            TyKeyPat = ty_of_pat(Ctx#ctx.symtab, Env, KeyPat, upper),
            TyValPat = ty_of_pat(Ctx#ctx.symtab, Env, ValPat, upper),
            StrictCs = sets:from_list([
                {csubty, mk_locs("strict map generator key", LGen), KeyAlpha, TyKeyPat},
                {csubty, mk_locs("strict map generator value", LGen), ValAlpha, TyValPat}
            ]),

            {KeyPatCs, KeyPatEnv} = pat_env(Ctx, LGen, KeyAlpha, KeyPat),
            {ValPatCs, ValPatEnv} = pat_env(Ctx, LGen, ValAlpha, ValPat),
            PatEnv = maps:merge(KeyPatEnv, ValPatEnv),
            NewEnv = intersect_envs(Env, PatEnv),
            process_qualifiers(Ctx, Loc, Qs, NewEnv, sets:union([Cs, ExpCs, KeyPatCs, ValPatCs, StrictCs]));
        % map generator: KeyPat := ValPat <- Exp
        {m_generate, LGen, KeyPat, ValPat, Exp} ->
            KeyAlpha = fresh_tyvar(Ctx), % map key type
            ValAlpha = fresh_tyvar(Ctx), % map value type
            KeyBeta = fresh_tyvar(Ctx), % key pattern type
            ValBeta = fresh_tyvar(Ctx), % value pattern type

            {ExpCs, _ExpEnv} = exp_constrs(Ctx, Exp, stdtypes:tmap(KeyAlpha, ValAlpha)),

            % Get upper bounds for filtering
            TyKeyPat = ty_of_pat(Ctx#ctx.symtab, Env, KeyPat, upper),
            TyValPat = ty_of_pat(Ctx#ctx.symtab, Env, ValPat, upper),

            {KeyPatCs, KeyPatEnv} = pat_env(Ctx, LGen, KeyBeta, KeyPat),
            {ValPatCs, ValPatEnv} = pat_env(Ctx, LGen, ValBeta, ValPat),

            % Filtering constraints for both key and value
            GeneratorC = [
                          {csubty, mk_locs("key pattern lower bound", LGen), ast_lib:mk_intersection([KeyAlpha, TyKeyPat]), KeyBeta},
                          {csubty, mk_locs("key pattern upper bound", LGen), KeyBeta, KeyAlpha},
                          {csubty, mk_locs("value pattern lower bound", LGen), ast_lib:mk_intersection([ValAlpha, TyValPat]), ValBeta},
                          {csubty, mk_locs("value pattern upper bound", LGen), ValBeta, ValAlpha}
                         ],
            PatEnv = maps:merge(KeyPatEnv, ValPatEnv),
            NewEnv = intersect_envs(Env, PatEnv),
            process_qualifiers(Ctx, Loc, Qs, NewEnv, sets:union([Cs, ExpCs, KeyPatCs, ValPatCs, sets:from_list(GeneratorC)]));
        % Filter expression
        % be careful here,
        % the catch-all will handle cases that are not supposed to be filters
        % this can happen when a new feature is introduced (e.g. zip, strict_generate)
        Filter ->
            % apply current environment to filter expression
            {FilterExpCs, FilterEnv} = exps_constrs(Ctx, Loc, [Filter], stdtypes:tbool()),
            FilterCs = sets:from_list([{cdef, mk_locs("filter", Loc), Env, FilterExpCs}]),

            % treat filter as if it is a guard to refine existing variable types
            % guard_seq_env cannot be applied to any expression, 
            % but the default case is unsafe, so we do it anyway
            {GuardEnv, _} = guard_seq_env([[Filter]]),
            I = intersect_envs(Env, GuardEnv),
            NewEnv = intersect_envs(I, FilterEnv),
            process_qualifiers(Ctx, Loc, Qs, NewEnv, sets:union(Cs, FilterCs))
    end.

-spec gen_funcall_constrs(ctx(), ast:loc(), ast:exp(), [ast:exp()], ast:ty()) -> constr:constrs().
gen_funcall_constrs(Ctx, L, FunExp, Args, T) ->
    {ArgCs, ArgTys} =
        lists:foldr(
            fun(ArgExp, {AccCs, AccTys}) ->
                    Alpha = fresh_tyvar(Ctx),
                    {Cs, _Env} = exp_constrs(Ctx, ArgExp, Alpha),
                    {sets:union(AccCs, Cs), [Alpha | AccTys]}
            end,
            {sets:new([{version, 2}]), []},
            Args),
    Beta = fresh_tyvar(Ctx),
    FunTy = {fun_full, ArgTys, Beta},
    {FunCs, _FunEnv} = exp_constrs(Ctx, FunExp, FunTy),
    Description =
        case FunExp of
            {var, _, AnyRef} ->
                "result of calling " ++ pretty:render_any_ref(AnyRef);
            _ -> "result of function call"
        end,
    sets:add_element(
        {csubty, mk_locs(Description, L), Beta, T},
        sets:union(FunCs, ArgCs)).

-spec var_funcall_constrs(ctx(), ast:loc(), ast:exp_var(), [ast:exp()], ast:ty()) -> constr:constrs().
var_funcall_constrs(Ctx, L, Var, Args, T) ->
    case var_as_global_ref(Var) of
        error -> gen_funcall_constrs(Ctx, L, Var, Args, T);
        {ok, Ref} ->
            case symtab:find_fun(Ref, Ctx#ctx.symtab) of
                error -> gen_funcall_constrs(Ctx, L, Var, Args, T);
                {ok, TyScm} ->
                    funcall_constrs_with_tyscm(Ctx, L, Var, TyScm, Args, T)
            end
    end.

-spec funcall_constrs_with_tyscm(ctx(), ast:loc(), ast:exp_var(), ast:ty_scheme(), [ast:exp()], ast:ty()) -> constr:constrs().
funcall_constrs_with_tyscm(Ctx, L, Var, TyScm, Args, T) ->
    {Mono, _, _} = typing_common:mono_ty(L, TyScm, none, fun(_, none) -> {fresh_ty_varname(Ctx), none} end, Ctx#ctx.symtab),
    case Mono of
        {fun_full, ArgTys, ResTy} when length(Args) =:= length(ArgTys) ->
            FunName = pretty:render_var(Var),
            ResConstr =
                {csubty,
                    mk_locs(utils:sformat("result of calling ~s", FunName), L),
                    ResTy,
                    T},
            Res = lists:foldr(
                fun({Arg, Ty}, Cs) ->
                    {ThisCs, _ThisEnv} = exp_constrs(Ctx, Arg, Ty),
                    sets:union(Cs, ThisCs)
                end,
                utils:single(ResConstr),
                lists:zip(Args, ArgTys)),
            ?LOG_DEBUG("Generating specialized constraints for call of fun ~s with type ~s (type scheme: ~s)",
                FunName, pretty:render_ty(Mono), pretty:render_tyscheme(TyScm)),
            Res;
        _ ->
            gen_funcall_constrs(Ctx, L, Var, Args, T)
    end.

-spec var_as_global_ref(ast:exp_var()) -> t:opt(ast:global_ref()).
var_as_global_ref({var, _, Ref}) ->
    case Ref of
        {local_ref, _} -> error;
        _ -> {ok, Ref}
    end.

% Generates constraints for a dynamic function call (Mod:Fun(Args)).
% Arguments are constrained to dynamic(), result is dynamic().
-spec dyncall_constrs(ctx(), ast:loc(), ast:exp(), ast:exp(), [ast:exp()], ast:ty()) -> constr:constrs().
dyncall_constrs(Ctx, L, ModExp, FunExp, Args, T) ->
    {ModCs, _} = exp_constrs(Ctx, ModExp, {predef, dynamic}),
    {FunCs, _} = exp_constrs(Ctx, FunExp, {predef, dynamic}),
    ArgCs = lists:foldr(
        fun(ArgExp, AccCs) ->
            {Cs, _} = exp_constrs(Ctx, ArgExp, {predef, dynamic}),
            sets:union(AccCs, Cs)
        end,
        sets:new([{version, 2}]),
        Args),
    ResultCs = utils:single({csubty, mk_locs("result of dynamic call", L), {predef, dynamic}, T}),
    sets:union([ModCs, FunCs, ArgCs, ResultCs]).

-spec ty_without(ast:ty(), ast:ty()) -> ast:ty().
ty_without(T1, T2) -> ast_lib:mk_intersection([T1, ast_lib:mk_negation(T2)]).

% Generates constraints for a receive expression.
% Pattern variables are bound to dynamic() since we don't know message types.
% Guards override dynamic with specific types (e.g., is_integer(X) makes X :: integer()).
-spec receive_constrs(ctx(), ast:loc(), [ast:case_clause()], ast:ty()) ->
    {constr:constrs(), constr:constr_env()}.
receive_constrs(Ctx, _L, CaseClauses, T) ->
    ClauseCs = lists:map(
        fun(Clause) -> receive_clause_constrs(Ctx, Clause, T) end,
        CaseClauses),
    {sets:union(ClauseCs), #{}}.

% Generates constraints for a receive...after expression.
% Combines receive clause constraints with the after body constraints.
-spec receive_after_constrs(ctx(), ast:loc(), [ast:case_clause()], ast:exp(), [ast:exp()], ast:ty()) ->
    {constr:constrs(), constr:constr_env()}.
receive_after_constrs(Ctx, L, CaseClauses, TimeoutExp, AfterBody, T) ->
    % Generate constraints for timeout expression
    {TimeoutCs, _TimeoutEnv} = exp_constrs(Ctx, TimeoutExp, {union, [{predef, integer}, {singleton, infinity}]}),
    % Generate constraints for the after body
    Beta = fresh_tyvar(Ctx),
    {AfterCs, _AfterEnv} = exps_constrs(Ctx, L, AfterBody, Beta),
    AfterResultCs = utils:single({csubty, mk_locs("receive after result", L), Beta, T}),
    % Generate constraints for receive clauses
    ClauseCs = lists:map(
        fun(Clause) -> receive_clause_constrs(Ctx, Clause, T) end,
        CaseClauses),
    {sets:union([TimeoutCs, AfterCs, AfterResultCs | ClauseCs]), #{}}.

% Generates constraints for a single receive clause.
% Pattern variables get type dynamic(). Guards override with specific types.
-spec receive_clause_constrs(ctx(), ast:case_clause(), ast:ty()) -> constr:constrs().
receive_clause_constrs(Ctx, {case_clause, L, Pat, Guards, Exps}, T) ->
    % Bind pattern variables to dynamic
    BoundVars = bound_vars_pat(Pat),
    DynamicPatEnv = sets:fold(
        fun(V, Acc) -> maps:put({local_ref, V}, {predef, dynamic}, Acc) end,
        #{},
        BoundVars),
    % Guard environment may refine variable types
    {GuardEnv, _} = guard_seq_env(Guards),
    % TODO think about why we can't intersect with dynamic() here
    %      recv_05_fail won't fail if we do
    VarEnv = maps:merge(DynamicPatEnv, GuardEnv),
    % Generate guard constraints to evaluate to boolean()
    GuardCs = sets:union(
        lists:map(
            fun(Guard) ->
                {Cs, _} = exps_constrs(Ctx, L, Guard, {predef_alias, boolean}),
                Cs
            end,
            Guards)),
    % Generate body constraints
    Beta = fresh_tyvar(Ctx),
    {BodyCs, _BodyEnv} = exps_constrs(Ctx, L, Exps, Beta),
    ResultCs = utils:single({csubty, mk_locs("receive clause result", L), Beta, T}),
    % Wrap in cdef with variable bindings
    InnerCs = sets:union([GuardCs, BodyCs, ResultCs]),
    utils:single({cdef, mk_locs("receive clause", L), VarEnv, InnerCs}).

% Check if a pattern contains a binary pattern at the top level (possibly inside a tuple).
-spec has_bin_pat(ast:pat()) -> boolean().
has_bin_pat({bin, _, _}) -> true;
has_bin_pat({tuple, _, Ps}) -> lists:any(fun has_bin_pat/1, Ps);
has_bin_pat({match, _, P1, P2}) -> has_bin_pat(P1) orelse has_bin_pat(P2);
has_bin_pat(_) -> false.

-spec needs_unmatched_check(list(ast:case_clause())) -> boolean().
needs_unmatched_check(Clauses) ->
    case Clauses of
        [{case_clause, _, Pat, [], _}] ->
            case Pat of
                {wildcard, _} -> false;
                {var, _, _} -> false;
                _ -> true
            end;
        _ -> true
    end.

% Computes the redudance constraints of a case clause. The clause is redudandant iff the
% constraints are satisfiable.
% Parameters:
%   ctx(): context
%   list(ast:ty()): accepting types (lower bound) of the guarded patterns of the branches
%       coming *before* the current branch
%   ast:ty(): potential type of the guarded pattern of the current branch
%   ast:exp(): scrutiny of the whole case
% Result:
%   constr:constr_case_branc_cond(): set of constraints
-spec case_clause_unmatched_constraints(ctx(), list(ast:ty()), ast:ty(), ast:exp()) ->
    constr:constr_case_branch_cond().
case_clause_unmatched_constraints(Ctx, LowersBefore, Upper, Scrut) ->
    Ui = ast_lib:mk_union([ast_lib:mk_negation(Upper) | LowersBefore]),
    {Cs, _Env} = scrut_constrs_compact(Ctx, Scrut, Ui),
    Cs.

% Like exp_constrs but optimized for scrutiny expressions that are tuples of
% variables. For each variable element, directly materializes it into the tuple
% type, skipping the intermediate fresh type variable that exp_constrs creates.
% Falls back to exp_constrs for non-tuple or non-variable-only scrutinies.
-spec scrut_constrs_compact(ctx(), ast:exp(), ast:ty()) -> {constr:constrs(), constr:constr_env()}.
scrut_constrs_compact(Ctx, {tuple, L, Args}, T) ->
    case lists:all(fun({var, _, _}) -> true; (_) -> false end, Args) of
        true ->
            {Tys, Cs} = lists:foldr(
                fun({var, VL, AnyRef}, {AccTys, AccCs}) ->
                    AlphaName = fresh_ty_varname(Ctx),
                    Msg = utils:sformat("var ~s", pretty:render(pretty:ref(AnyRef))),
                    Locs = mk_locs(Msg, VL),
                    Mater = {cvarmater, Locs, AnyRef, AlphaName},
                    {[{var, AlphaName} | AccTys], sets:add_element(Mater, AccCs)}
                end,
                {[], sets:new([{version, 2}])},
                Args),
            TupleC = {csubty, mk_locs("tuple constructor", L), {tuple, Tys}, T},
            {sets:add_element(TupleC, Cs), #{}};
        false ->
            exp_constrs(Ctx, {tuple, L, Args}, T)
    end;
scrut_constrs_compact(Ctx, Scrut, T) ->
    exp_constrs(Ctx, Scrut, T).

% Parameters:
%   ctx(): context
%   ast:ty(): type of scrutiny (alpha in the typing rules)
%   ast:exp(): scrutiny of the case
%   boolean(): true if this case branch needs a redudancy check
%   list(ast:ty()): accepting types (lower bound) of the guarded patterns of the branches
%       coming *before* the current branch
%   ast:case_clause(): cause clause
%   ast:ty(): expected ty from the outer context (the "t" in the typing rules).
%             We generate a separate constraint for each clause for better error messages.
% Result:
%   ast:ty(): accepting type (lower bound) of the guarded pattern of the clause
%   ast:ty(): potential type (upper bound) of the guarded pattern of the clause
%   constr:constrs(): constraints result from the guarded pattern of the clause
%   constr:constr_case_branch(): the body of the case
-spec case_clause_constrs(
    ctx(), ast:ty(), ast:exp(), constr:constr_env(), boolean(), list(ast:ty()), ast:case_clause(), ast:ty()
) -> {ast:ty(), ast:ty(), constr:constrs(), constr:constr_case_branch(), constr:constr_env()}.
case_clause_constrs(Ctx, TyScrut, Scrut, ScrutEnv, NeedsUnmatchedCheck, LowersBefore,
    {case_clause, L, Pat, Guards, Exps}, ExpectedTy) ->
    {BodyLower, BodyUpper, BodyEnvCs, BodyEnv0} =
        case_clause_env(Ctx, L, TyScrut, Scrut, Pat, Guards),
    % When there are no guards and the pattern has no variables, both calls to
    % case_clause_env produce identical results (same inputs), so we can reuse
    % the body env for the guard env, saving fresh type variable allocations.
    {GuardEnvCs, GuardEnv0} =
        case Guards == [] andalso not pat_has_vars(Pat) of
            true -> {BodyEnvCs, BodyEnv0};
            false ->
                {_, _, GCs, GEnv} = case_clause_env(Ctx, L, TyScrut, Scrut, Pat, []),
                {GCs, GEnv}
        end,
    % Variables bound in the scrutinee expression (e.g. case U = ok of ...)
    % must be visible in the clause body and guard environments.
    BodyEnv = intersect_envs(ScrutEnv, BodyEnv0),
    GuardEnv = intersect_envs(ScrutEnv, GuardEnv0),
    ?LOG_TRACE("TyScrut=~s, Scrut=~w, GuardEnv=~s, GuardEnvCs=~s, BodyEnv=~s, BodyEnvCs=~s",
        pretty:render_ty(TyScrut),
        Scrut,
        pretty:render_mono_env(GuardEnv),
        pretty:render_constr(GuardEnvCs),
        pretty:render_mono_env(BodyEnv),
        pretty:render_constr(BodyEnvCs)
    ),
    % Pass ExpectedTy directly as the target for the body expression,
    % eliminating the intermediate Beta variable and its result constraint.
    {InnerCs, InnerSafeEnv} = exps_constrs(Ctx, L, Exps, ExpectedTy),

    % Merge pattern/guard environment with variables bound in body
    CompleteBodyEnv = intersect_envs(BodyEnv, InnerSafeEnv),

    CGuards =
        sets:union(
          lists:map(
            fun(Guard) ->
                    {GuardCs, _GuardEnv} = exps_constrs(Ctx, L, Guard, {predef_alias, boolean}),
                    GuardCs
            end,
            Guards)),
    RedundancyCs =
        if
            NeedsUnmatchedCheck ->
                case_clause_unmatched_constraints(Ctx, LowersBefore, BodyUpper, Scrut);
            true -> none
        end,
    Payload = constr:mk_case_branch_payload(
        {GuardEnv, CGuards}, {BodyEnv, InnerCs}, RedundancyCs, sets:new([{version, 2}])),
    ConstrBody = {ccase_branch, mk_locs("case branch", L), Payload},
    AllCs = sets:union([BodyEnvCs, GuardEnvCs]),
    {BodyLower, BodyUpper, AllCs, ConstrBody, CompleteBodyEnv}.

% Generates constraints for a catch clause in a try-catch expression.
% Parameters:
%   ctx(): context
%   ast:catch_clause(): the catch clause
%   ast:ty(): expected type from outer context
% Result:
%   constr:constrs(): constraints from the catch clause pattern and guards
%   constr:constr_case_branch(): the body of the catch clause
%   constr:constr_env(): environment from catch clause body (unsafe outside try-catch)
-spec catch_clause_constrs(ctx(), ast:catch_clause(), ast:ty()) ->
    {constr:constrs(), constr:constr_case_branch(), constr:constr_env()}.
catch_clause_constrs(Ctx, {catch_clause, L, ExcType, Pat, Stack, Guards, Body}, ExpectedTy) ->
    % Create environment from exception type, pattern, and stacktrace bindings
    {PatCs, PatEnv0} = catch_clause_pat_env(Ctx, L, ExcType, Pat, Stack),

    % Apply guards to refine the environment (guards only refine, no constraints)
    {GuardEnv, _GuardStatus} = guard_seq_env(Guards),
    PatEnv = intersect_envs(PatEnv0, GuardEnv),

    % Generate constraints for body in the refined environment
    Beta = fresh_tyvar(Ctx),
    InnerCs0 = sets:union(PatCs, sets:new([{version, 2}])),
    {BodyCs, BodySafeEnv} = exps_constrs(Ctx, L, Body, Beta),
    InnerCs = sets:union(BodyCs, InnerCs0),

    % Result type constraint
    ResultLocs = mk_locs("catch clause result", L),
    ResultCs = utils:single({csubty, ResultLocs, Beta, ExpectedTy}),

    % Create branch payload with pattern environment
    % The pattern environment needs to be wrapped in cdef
    BodyWithEnv = sets:from_list([{cdef, mk_locs("catch clause", L), PatEnv, InnerCs}], [{version, 2}]),
    Payload = constr:mk_case_branch_payload(
        {GuardEnv, sets:new()},  % Guard constraints (guards don't generate constraints)
        {BodySafeEnv, BodyWithEnv},  % Body constraints with env
        none,                     % No redundancy check for catch
        ResultCs),                % Result constraint
    ConstrBody = {ccase_branch, mk_locs("catch clause", L), Payload},

    % Return pattern constraints (like case_clause_constrs returns pattern/guard constraints)
    {PatCs, ConstrBody, BodySafeEnv}.

% Helper for catch_clause_constrs: generate environment from exception pattern
-spec catch_clause_pat_env(ctx(), ast:loc(), ast:exc_type_pat(), ast:pat(), ast:stacktrace_pat()) ->
    {constr:constrs(), constr:constr_env()}.
catch_clause_pat_env(Ctx, L, ExcType, Pat, Stack) ->
    % Exception type can be a variable, wildcard, or atom (throw/error/exit)
    ExcTypeEnv = case ExcType of
        {var, _VarLoc, {local_bind, Name}} ->
            % Exception type is bound to a variable - it's an atom (throw/error/exit)
            % Use explicit union type since there's no predef_alias for exception classes
            ExcTypeAtom = {union, [{singleton, throw}, {singleton, error}, {singleton, exit}]},
            #{{local_ref, Name} => ExcTypeAtom};
        _ ->
            % Wildcard or atom - no binding
            #{}
    end,

    % Stacktrace can be a variable or wildcard
    StackEnv = case Stack of
        {var, _StackLoc, {local_bind, StackName}} ->
            % Stacktrace is bound to a variable - type is any() (list of stack frames)
            StackTy = {predef, any},
            #{{local_ref, StackName} => StackTy};
        _ ->
            % Wildcard - no binding
            #{}
    end,

    % Pattern binds the exception value - we use `any()` as exception value type
    ExceptionValueTy = {predef, any},
    {PatCs, PatEnv} = pat_env(Ctx, L, ExceptionValueTy, Pat),

    % Merge all environments
    CombinedEnv = maps:merge(maps:merge(ExcTypeEnv, StackEnv), PatEnv),
    {PatCs, CombinedEnv}.

% helper function for case_clause_constrs
-spec case_clause_env(ctx(), ast:loc(), ast:ty(), ast:exp(), ast:pat(), [ast:guard()]) ->
          {ast:ty(), ast:ty(), constr:constrs(), constr:constr_env()}.
case_clause_env(Ctx, L, TyScrut, Scrut, Pat, Guards) ->
    {Lower, Upper} = pat_guard_lower_upper(Ctx#ctx.symtab, Pat, Guards, Scrut),
    Ti = ast_lib:mk_intersection([TyScrut, Upper]),
    {Ci0, Gamma0} = pat_env(Ctx, L, Ti, pat_of_exp(Scrut)),
    % Skip pattern decomposition when the pattern has no variables,
    % since no environment bindings would be produced.
    % But still include guard refinements, as guards may refine outer variables.
    {Ci1, Gamma1} =
        case pat_has_vars(Pat) of
            false ->
                {EnvGuards, _} = guard_seq_env(Guards),
                {sets:new([{version, 2}]), EnvGuards};
            true -> pat_guard_env(Ctx, L, Ti, Pat, Guards)
        end,
    Gamma2 = intersect_envs(Gamma1, Gamma0),
    {Lower, Upper, sets:union(Ci0, Ci1), Gamma2}.

% ⌊ p when g ⌋_e and ⌈ p when g ⌉_e
-spec pat_guard_lower_upper(symtab:t(), ast:pat(), [ast:guard()], ast:exp()) -> {ast:ty(), ast:ty()}.
pat_guard_lower_upper(Symtab, P, Gs, E) ->
    EPat = pat_of_exp(E),
    BoundVars = sets:union(bound_vars_pat(P), bound_vars_pat(EPat)),
    % Compute Lower and Upper as unions over disjunctive guard branches.
    % For 'or' guards like is_atom(X) or is_atom(Y), each branch contributes
    % a separate bound, and the union gives: {atom, any} | {any, atom}.
    % Both Upper and Lower must be computed disjunctively so they stay consistent
    DisjEnvs = guard_seq_lower_envs(Gs),
    Upper =
        ast_lib:mk_union(
            lists:map(
                fun({UEnv, _}) ->
                    UpperPatTy = ty_of_pat(Symtab, UEnv, P, upper),
                    UpperETy = ty_of_pat(Symtab, UEnv, EPat, upper),
                    ast_lib:mk_intersection([UpperPatTy, UpperETy])
                end,
                DisjEnvs)),
    Lower =
        ast_lib:mk_union(
            lists:map(
                fun({LEnv, LStatus}) ->
                    LVarsOfGuards = sets:from_list(
                        lists:filtermap(fun ast:local_varname_from_any_ref/1, maps:keys(LEnv))),
                    case {LStatus, sets:is_subset(LVarsOfGuards, BoundVars)} of
                        {safe, true} ->
                            LowerPatTy = ty_of_pat(Symtab, LEnv, P, lower),
                            LowerETy = ty_of_pat(Symtab, LEnv, EPat, lower),
                            ast_lib:mk_intersection([LowerPatTy, LowerETy]);
                        _ -> {predef, none}
                    end
                end,
                DisjEnvs)),
    ?LOG_TRACE("EPat=~200p, Upper=~s, Lower=~s, BoundVars=~w, DisjEnvs=~w",
               EPat,
               pretty:render_ty(Upper),
               pretty:render_ty(Lower),
               sets:to_list(BoundVars),
               length(DisjEnvs)),
    {Lower, Upper}.

% The variables bound by a pattern
-spec bound_vars_pat(ast:pat()) -> sets:set(ast:local_varname()).
bound_vars_pat(P) ->
    case P of
        {'atom', _L, _A} -> sets:new([{version, 2}]);
        {'char', _L, _C} -> sets:new([{version, 2}]);
        {'integer', _L, _I} -> sets:new([{version, 2}]);
        {'float', _L, _F} -> sets:new([{version, 2}]);
        {'string', _L, _S} -> sets:new([{version, 2}]);
        % TODO correct bounded vars for bitstring patterns
        {bin, _L, Elems} -> 
            lists:foldl(
                fun(P, Acc) -> sets:union(Acc, bound_vars_pat(P)) end, 
                sets:new([{version, 2}]), 
                Elems);
        default -> sets:new([{version, 2}]); % gen_bitstring_elem
        {bin_element, _L, Value, Size, _TyspecList} -> 
            % Size can have bound vars
            % TyspecList is static
            sets:union(bound_vars_pat(Value), bound_vars_pat(Size));
        {match, _L, P1, P2} ->
            sets:union(bound_vars_pat(P1), bound_vars_pat(P2));
        {nil, _L} -> sets:new([{version, 2}]);
        {cons, _L, P1, P2} ->
            sets:union(bound_vars_pat(P1), bound_vars_pat(P2));
        {op, _L, _Op, Ps} ->
            lists:foldl(
              fun(P, Acc) -> sets:union(Acc, bound_vars_pat(P)) end,
              sets:new([{version, 2}]),
              Ps
             );
        {map, _L, Assocs} ->
            lists:foldl(
              % NOTE: the key part of a map pattern does not bound variables
              fun({map_field_req, _L, _P1, P2}, Acc) -> sets:union(Acc, bound_vars_pat(P2)) end,
              sets:new([{version, 2}]),
              Assocs
             );
        {record, _L, _RecName, FieldPatterns} ->
            lists:foldl(
              fun({record_field, _L, _FieldName, P}, Acc) -> sets:union(Acc, bound_vars_pat(P)) end,
              sets:new([{version, 2}]),
              FieldPatterns
             );
        {record_index, _L, _Name, _Field} -> sets:new([{version, 2}]);
        {tuple, _L, Ps} ->
            lists:foldl(
              fun(P, Acc) -> sets:union(Acc, bound_vars_pat(P)) end,
              sets:new([{version, 2}]),
              Ps
             );
        {wildcard, _L} -> sets:new([{version, 2}]);
        {var, _L, {local_bind, V}} -> sets:from_list([V], [{version, 2}]);
        {var, _L, {local_ref, _V}} -> sets:new([{version, 2}])
    end.

% Returns true if the pattern contains any variable bindings or references.
% Used to skip fresh variable creation in pat_env when a sub-pattern
% has no variables (the decomposition constraints would be wasted).
-spec pat_has_vars(ast:pat()) -> boolean().
pat_has_vars(P) ->
    case P of
        {var, _, _} -> true;
        {tuple, _, Ps} -> lists:any(fun pat_has_vars/1, Ps);
        {cons, _, P1, P2} -> pat_has_vars(P1) orelse pat_has_vars(P2);
        {match, _, P1, P2} -> pat_has_vars(P1) orelse pat_has_vars(P2);
        {map, _, Assocs} ->
            lists:any(fun({map_field_req, _, _PK, PV}) -> pat_has_vars(PV) end, Assocs);
        {record, _, _, FieldPats} ->
            lists:any(fun({record_field, _, _, FP}) -> pat_has_vars(FP) end, FieldPats);
        {op, _, _, Ps} -> lists:any(fun pat_has_vars/1, Ps);
        {bin, _, Elems} ->
            lists:any(fun({bin_element, _, Value, _, _}) -> pat_has_vars(Value);
                         (Other) -> pat_has_vars(Other) end, Elems);
        _ -> false
    end.

% ty_of_pat
% \lbag p \rbag_\Gamma
%
% In the paper, the type t of a pattern p has the following semantics:
%     Expression e matches p if, and only if, e has type t
%
% For existing variables, this is no longer true.
%
% Hence, we introduce a mode for ty_of_pat, which can be either upper or lower.
%
% - Mode upper deals with the potential type. Any expression matching p must
%   be of this type.
%
% - Mode lower deals with the accepting type. If e has this type, then p definitely
%   matches.
-spec ty_of_pat(symtab:t(), constr:constr_env(), ast:pat(), upper | lower) -> ast:ty().
ty_of_pat(Symtab, Env, P, Mode) ->
    case P of
        {'atom', _L, A} -> {singleton, A};
        {'char', _L, C} -> {singleton, C};
        {'integer', _L, I} -> {singleton, I};
        {'float', _L, _F} -> {predef, float};
        {'string', _L, []} -> {empty_list};
        {'string', _L, Z} -> 
            [X|Xs] = lists:reverse(Z),
            lists:foldl(fun(E, Acc) -> {cons, {singleton, E}, Acc} end, {cons, {singleton, X}, {empty_list}}, Xs);
        {bin, _L, []} -> {bitstring, 0, 0};
        {bin, _L, Elems} -> ty_of_bin_pat(Elems, Mode);
        {match, _L, P1, P2} ->
            ast_lib:mk_intersection([ty_of_pat(Symtab, Env, P1, Mode), ty_of_pat(Symtab, Env, P2, Mode)]);
        {nil, _L} -> {empty_list};
        {cons, _L, P1, P2} ->
            T1 = ty_of_pat(Symtab, Env, P1, Mode),
            T2 = ty_of_pat(Symtab, Env, P2, Mode),
            {cons, T1, T2};
        {op, _, '++', [P1, P2]} ->
            ast_lib:mk_intersection([ty_of_pat(Symtab, Env, P1, Mode), ty_of_pat(Symtab, Env, P2, Mode),
                                 {predef_alias, string}]);
        {op, _, '-', [{integer, _L2, I}]} ->
            {singleton, -I};
        {op, _, '-', [SubP]} ->
            ast_lib:mk_intersection([ty_of_pat(Symtab, Env, SubP, Mode), {predef_alias, number}]);
        {op, L, Op, _} -> errors:unsupported(L, "operator ~w in patterns", Op);
        {map, _L, []} ->
            Any = stdtypes:tany(),
            stdtypes:tmap(Any, Any);
        {map, _L, Assocs} ->
            {KeyTs, ValTs} =
                lists:foldl(
                    fun({map_field_req, _, KeyP, ValP}, {KeyTs, ValTs}) ->
                        K = ty_of_pat(Symtab, Env, KeyP, Mode),
                        V = ty_of_pat(Symtab, Env, ValP, Mode),
                        {[K | KeyTs], [V | ValTs]}
                    end,
                    {[], []},
                    Assocs),
            F =
                case Mode of
                    upper -> fun ast_lib:mk_union/1;
                    lower -> fun ast_lib:mk_intersection/1
                end,
            stdtypes:tmap_req(F(KeyTs), F(ValTs));
        {record, L, RecName, FieldPats} ->
            {_, RecFields} = symtab:lookup_record(RecName, L, Symtab),
            FieldMap =
                lists:foldl(
                    fun({record_field, FieldLoc, FieldName, FieldPat}, FieldMap) ->
                        case maps:find(FieldName, FieldMap) of
                            {ok, _} ->
                                errors:ty_error(FieldLoc,
                                    "Duplicated label ~w in record pattern",
                                    [FieldName]);
                            _ -> ok
                        end,
                        Ty = ty_of_pat(Symtab, Env, FieldPat, Mode),
                        maps:put(FieldName, Ty, FieldMap)
                    end,
                    #{},
                    FieldPats),
            MatchedRecFields =
                lists:map(
                    fun({FieldName, _}) ->
                        case maps:find(FieldName, FieldMap) of
                            {ok, Ty} -> {FieldName, Ty};
                            _ -> {FieldName, stdtypes:tany()}
                        end
                    end,
                    RecFields),
            TupleTy = records:encode_record_ty({RecName, MatchedRecFields}),
            TupleTy;
        {record_index, L, RecName, FieldName} ->
            RecTy = symtab:lookup_record(RecName, L, Symtab),
            {_, Idx} = records:lookup_field_index(RecTy, FieldName, L),
            stdtypes:tint(Idx + 1);
        {tuple, _L, Ps} -> {tuple, lists:map(fun(P) -> ty_of_pat(Symtab, Env, P, Mode) end, Ps)};
        {wildcard, _L} -> {predef, any};
        {var, _L, {local_bind, V}} ->
            % V binds a fresh variable
            maps:get({local_ref, V}, Env, stdtypes:tany());
        {var, _L, _Ref} ->
            % V refers to an existing variable
            % We are conservative (and pragmatic) here and return any() for the upper and none()
            % for the lower bound. Here is an artifical example where we could do better:
            % -spec case_13_fail(1, 1) -> 2.
            % case_13_fail(X, A) ->
            %   case A of
            %     X -> 2
            %   end.
            % The type checker fails with "not all cases are covered" By using 1 as the type of
            % the upper bound, it would recognize that all cases are covered. In the given
            % function, it seems easy to use 1 as the upper bound type. But what happens if
            % X is not a parameter with an annotated type, but a local variables with an
            % inferred type?
            % SW (2024-10-14) believes that such situations are rare.
            case Mode of
                upper -> stdtypes:tany();
                lower -> stdtypes:tnone()
            end
    end.

% Compute the type of a non-empty binary pattern.
% Upper bound: what types CAN match. Lower bound: what types DEFINITELY match.
-spec ty_of_bin_pat([ast:gen_bitstring_elem(ast:pat(), ast:exp())], upper | lower) -> ast:ty().
ty_of_bin_pat(Elems, Mode) ->
    % Analyze each element for fixed bits and alignment
    {TotalFixedBits, HasRestBinary, HasRestBitstring, AllByteAligned, AllDefinite, AllFixed} =
        lists:foldl(
            fun({bin_element, _, Value, Size, TyspecList}, {AccBits, AccRestBin, AccRestBits, AccAligned, AccDef, AccFixed}) ->
                {SegType, _Signed, DefaultSize, Unit} = analyze_bin_tyspec(TyspecList),
                IsDefinite = is_definite_match(Value),
                case {Size, DefaultSize, SegType} of
                    {default, default, binary} ->
                        % Rest binary segment (e.g., _/binary): consumes remaining, byte-aligned
                        {AccBits, true, AccRestBits, AccAligned, AccDef andalso IsDefinite, false};
                    {default, default, bitstring} ->
                        % Rest bitstring segment (e.g., _/bitstring): consumes remaining, any alignment
                        {AccBits, AccRestBin, true, false, AccDef andalso IsDefinite, false};
                    {default, default, utf8} ->
                        {AccBits, AccRestBin, AccRestBits, AccAligned, false, false};
                    {default, default, utf16} ->
                        {AccBits, AccRestBin, AccRestBits, AccAligned, false, false};
                    {default, default, utf32} ->
                        {AccBits + 32, AccRestBin, AccRestBits, AccAligned, AccDef andalso IsDefinite, AccFixed};
                    {default, DS, _} ->
                        Bits = DS * Unit,
                        {AccBits + Bits, AccRestBin, AccRestBits, AccAligned andalso (Bits rem 8 =:= 0),
                         AccDef andalso IsDefinite, AccFixed};
                    {{integer, _, V}, _, _} when is_integer(V) ->
                        Bits = V * Unit,
                        {AccBits + Bits, AccRestBin, AccRestBits, AccAligned andalso (Bits rem 8 =:= 0),
                         AccDef andalso IsDefinite, AccFixed};
                    _ ->
                        % Variable size
                        {AccBits, AccRestBin, AccRestBits, AccAligned andalso (Unit rem 8 =:= 0),
                         AccDef andalso IsDefinite, false}
                end
            end,
            {0, false, false, true, true, true},
            Elems),
    case Mode of
        upper ->
            % Upper bound: what types CAN match this pattern
            case {AllByteAligned, HasRestBitstring} of
                {true, false} -> {bitstring, 0, 8};  % binary()
                _ -> {bitstring}  % any bitstring
            end;
        lower ->
            % Lower bound: what types DEFINITELY match this pattern
            case AllDefinite of
                false ->
                    % Pattern has literals or variable refs → can't guarantee match
                    {predef, none};
                true ->
                    case {AllFixed, HasRestBinary, HasRestBitstring} of
                        {true, false, false} ->
                            % All fixed size, no rest segment
                            {bitstring, TotalFixedBits, 0};
                        {_, true, false} ->
                            % Has rest binary segment (byte-aligned)
                            {bitstring, TotalFixedBits, 8};
                        {_, _, true} ->
                            % Has rest bitstring segment (any alignment)
                            {bitstring, TotalFixedBits, 1};
                        _ ->
                            {predef, none}
                    end
            end
    end.

% Check if a pattern value position is a "definite match" (wildcard or fresh bind).
-spec is_definite_match(ast:pat()) -> boolean().
is_definite_match({wildcard, _}) -> true;
is_definite_match({var, _, {local_bind, _}}) -> true;
is_definite_match(_) -> false.

% t // pg
-spec pat_guard_env(ctx(), ast:loc(), ast:ty(), ast:pat(), [ast:guard()]) ->
          {constr:constrs(), constr:constr_env()}.
pat_guard_env(Ctx, L, T, P, Gs) ->
    {Cs, Env} = pat_env(Ctx, L, T, P),
    {EnvGuards, _} = guard_seq_env(Gs),
    {Cs, intersect_envs(Env, EnvGuards)}.

% t // p
-spec pat_env(ctx(), ast:loc(), ast:ty(), ast:pat()) -> {constr:constrs(), constr:constr_env()}.
pat_env(Ctx, OuterL, T, P) ->
    Empty = {sets:new([{version, 2}]), #{}},
    case P of
        {'atom', _L, _A} -> Empty;
        {'char', _L, _C} -> Empty;
        {'integer', _L, _I} -> Empty;
        {'float', _L, _F} -> Empty;
        {'string', _L, _S} -> Empty;
        {bin, _L, []} ->
            C = {csubty, mk_locs("t // <<>>", OuterL), T, {bitstring, 0, 0}},
            {sets:from_list([C], [{version, 2}]), #{}};
        {bin, _L, Elems} ->
            BinTy = ty_of_bin_pat(Elems, upper),
            {Cs, Env} =
                lists:foldl(
                  fun (Elem, {AccCs, AccEnv}) ->
                          {ThisCs, ThisEnv} = bin_elem_pat_env(Ctx, OuterL, Elem),
                          {sets:union(AccCs, ThisCs),
                           intersect_envs(AccEnv, ThisEnv)}
                  end,
                  {sets:new([{version, 2}]), #{}},
                  Elems),
            C = {csubty, mk_locs("t // <<...>>", OuterL), T, BinTy},
            {sets:add_element(C, Cs), Env};
        default -> Empty;
        {match, _L, P1, P2} ->
            {Cs1, Env1} = pat_env(Ctx, OuterL, T, P1),
            {Cs2, Env2} = pat_env(Ctx, OuterL, T, P2),
            {sets:union(Cs1, Cs2), intersect_envs(Env1, Env2)};
        {nil, _L} ->
            Empty;
        {cons, L, P1, P2} ->
            Alpha1 = fresh_tyvar(Ctx),
            {Cs1, Env1} = pat_env(Ctx, L, Alpha1, P1),
            
            Alpha2 = fresh_tyvar(Ctx),
            {Cs2, Env2} = pat_env(Ctx, L, Alpha2, P2),

            NewEnv = intersect_envs(Env1, Env2),
            NewCs = sets:union(Cs1, Cs2),

            C = {csubty, mk_locs("t // [_ | _]", L), T, {cons, Alpha1, Alpha2}},

            {sets:add_element(C, NewCs), NewEnv};
        {op, _L, '++', [P1, P2]} ->
            {Cs1, Env1} = pat_env(Ctx, OuterL, T, P1),
            {Cs2, Env2} = pat_env(Ctx, OuterL, T, P2),
            {sets:union(Cs1, Cs2), intersect_envs(Env1, Env2)};
        {op, _L, '-', [SubP]} ->
            pat_env(Ctx, OuterL, T, SubP);
        {op, L, Op, _Ps} ->
            errors:unsupported(L, "operator ~w in patterns", Op);
        {map, _L, Assocs} ->
            AlphaK = fresh_tyvar(Ctx),
            AlphaV = fresh_tyvar(Ctx),
            {AssocCs, AssocEnv} =
                lists:foldl(
                    fun({map_field_req, _L, PK, PV}, {Cs, Env}) ->
                        {CK, _} = pat_env(Ctx, OuterL, AlphaK, PK),
                        {CV, EnvV} = pat_env(Ctx, OuterL, AlphaV, PV),
                        {sets:union([Cs, CK, CV]), intersect_envs(Env, EnvV)}
                    end,
                    {sets:new([{version, 2}]), #{}},
                    Assocs),
            C = {csubty, mk_locs("t // #{_}", OuterL), T, stdtypes:tmap(AlphaK, AlphaV)},
            {sets:add_element(C, AssocCs), AssocEnv};
        {record, L, RecName, FieldPats} ->
            {_, DefFields} = symtab:lookup_record(RecName, L, Ctx#ctx.symtab),
            {Cs, Env, MatchedFieldTypes} =
                lists:foldl(
                    fun ({record_field, _FieldLoc, FieldName, FieldPat}, {AccCs, AccEnv, AccFieldTypes}) ->
                        Alpha = fresh_tyvar(Ctx),
                        {ThisCs, ThisEnv} = pat_env(Ctx, OuterL, Alpha, FieldPat),
                        {sets:union(AccCs, ThisCs),
                            intersect_envs(AccEnv, ThisEnv),
                            maps:put(FieldName, Alpha, AccFieldTypes)}
                    end,
                    {sets:new([{version, 2}]), #{}, #{}},
                    FieldPats),
            FieldTypes =
                lists:map(
                    fun({FieldName, _DefFieldType}) ->
                        case maps:find(FieldName, MatchedFieldTypes) of
                            {ok, Ty} -> {FieldName, Ty};
                            error -> {FieldName, stdtypes:tany()}
                        end
                    end,
                    DefFields),
            RecTupleTy = records:encode_record_ty({RecName, FieldTypes}),
            C = {csubty, mk_locs("t // #Record{...}", OuterL), T, RecTupleTy},
            {sets:add_element(C, Cs), Env};
        {record_index, _L, _Name, _Field} -> Empty;
        {tuple, _L, Ps} ->
            {Alphas, Cs, Env} =
                lists:foldl(
                  fun (P, {Alphas, Cs, Env}) ->
                          case pat_has_vars(P) of
                              false ->
                                  % No variables bound in this element, use any() to
                                  % avoid creating an unused fresh type variable.
                                  {Alphas ++ [{predef, any}], Cs, Env};
                              true ->
                                  Alpha = fresh_tyvar(Ctx),
                                  {ThisCs, ThisEnv} = pat_env(Ctx, OuterL, Alpha, P),
                                  {Alphas ++ [Alpha],
                                   sets:union(Cs, ThisCs),
                                   intersect_envs(Env, ThisEnv)}
                          end
                  end,
                  {[], sets:new([{version, 2}]), #{}},
                  Ps),
            C = {csubty, mk_locs("t // {...}", OuterL), T, {tuple, Alphas}},
            {sets:add_element(C, Cs), Env};
        {wildcard, _L} ->
            Empty;
        {var, _L, {local_bind, V}} ->
            % V binds a fresh variable
            {sets:new([{version, 2}]), #{ {local_ref, V} => T }};
        {var, _L, LocalRef} ->
            % V refers to an existing variable
            {sets:new([{version, 2}]), #{ LocalRef => T }}
    end.

% Process a single bin_element in a binary pattern, computing proper types for Value and Size.
-spec bin_elem_pat_env(ctx(), ast:loc(), ast:gen_bitstring_elem(ast:pat(), ast:exp())) ->
    {constr:constrs(), constr:constr_env()}.
bin_elem_pat_env(Ctx, OuterL, {bin_element, _L, Value, Size, TyspecList}) ->
    {SegType, Signed, _, Unit} = analyze_bin_tyspec(TyspecList),
    ValueTy = case SegType of
        integer when Signed -> {predef, integer};
        integer -> {predef_alias, non_neg_integer};  % non_neg_integer for unsigned
        float -> {predef, float};
        binary when Unit =:= 8 -> {bitstring, 0, 8};
        binary -> {bitstring};  % binary with non-default unit accepts any bitstring
        bitstring -> {bitstring};
        utf8 -> {predef, integer};
        utf16 -> {predef, integer};
        utf32 -> {predef, integer}
    end,
    {Cs1, Env1} = pat_env(Ctx, OuterL, ValueTy, Value),
    {Cs2, Env2} = case Size of
        default -> {sets:new([{version, 2}]), #{}};
        _ -> pat_env(Ctx, OuterL, {predef, integer}, Size)
    end,
    {sets:union(Cs1, Cs2), intersect_envs(Env1, Env2)}.

% (| e |)
-spec pat_of_exp(ast:exp()) -> ast:pat().
pat_of_exp(E) ->
    Wc = {wildcard, ast:loc_auto()},
    case E of
        {block, _L, Es} ->
            case lists:reverse(Es) of
                [] -> Wc;
                [Last | _] -> pat_of_exp(Last)
            end;
        {cons, _L, Head, Tail} ->
            {cons, ast:loc_auto(), pat_of_exp(Head), pat_of_exp(Tail)};
        {tuple, _L, Args} ->
            {tuple, ast:loc_auto(), lists:map(fun pat_of_exp/1, Args)};
        {var, _L, {local_ref, V}} -> {var, ast:loc_auto(), {local_bind, V}};
        _ -> Wc
    end.

% Combines two environments key-wise using F. The Default parameter is the
% identity element used for keys missing from one environment:
%   any()  - identity for intersection (T /\ any() = T)
%   none() - identity for union (T \/ none() = T)
-spec combine_envs(
        constr:constr_env(),
        constr:constr_env(),
        fun((ast:ty(), ast:ty()) -> ast:ty()),
        ast:ty()
       ) -> constr:constr_env().
combine_envs(Env1, Env2, F, Default) ->
    Keys = sets:from_list(maps:keys(Env1) ++ maps:keys(Env2)),
    sets:fold(
      fun (K, Env) ->
              T1 = maps:get(K, Env1, Default),
              T2 = maps:get(K, Env2, Default),
              maps:put(K, F(T1, T2), Env)
      end,
      #{},
      Keys
     ).

% Γ //\\ Γ
-spec intersect_envs(constr:constr_env(), constr:constr_env()) -> constr:constr_env().
intersect_envs(Env1, Env2) ->
    combine_envs(Env1, Env2, fun(T1, T2) -> ast_lib:mk_intersection([T1, T2]) end, {predef, any}).

% Γ \\// Γ
% Missing keys default to any(): a variable unconstrained in one branch
% gives T \/ any() = any(), correctly losing the refinement.
-spec union_envs(constr:constr_env(), constr:constr_env()) -> constr:constr_env().
union_envs(Env1, Env2) ->
    combine_envs(Env1, Env2, fun(T1, T2) -> ast_lib:mk_union([T1, T2]) end, {predef, any}).

-spec negate_env(constr:constr_env()) -> constr:constr_env().
negate_env(Env) -> maps:map(fun (_Key, T) -> ast_lib:mk_negation(T) end, Env).

% Returns a list of disjunctive environments for computing Lower.
% For 'or' guards, each branch produces a separate environment.
% For 'and' guards, environments are intersected (Cartesian product).
% For other guards, falls back to guard_test_env.
-spec guard_test_lower_envs(ast:guard_test()) -> [{constr:constr_env(), safe | unsafe}].
guard_test_lower_envs(G) ->
    case G of
        {op, _L, Op, Left, Right} when Op =:= 'orelse'; Op =:= 'or' ->
            guard_test_lower_envs(Left) ++ guard_test_lower_envs(Right);
        {op, _L, Op, Left, Right} when Op =:= 'andalso'; Op =:= 'and' ->
            [{intersect_envs(EL, ER), merge_status(SL, SR)}
             || {EL, SL} <- guard_test_lower_envs(Left),
                {ER, SR} <- guard_test_lower_envs(Right)];
        _ ->
            [guard_test_env(G)]
    end.

% Like guard_env/1 but returns disjunctive environments.
% Tests within a guard are conjunctive (,) so we take the Cartesian product.
-spec guard_lower_envs(ast:guard()) -> [{constr:constr_env(), safe | unsafe}].
guard_lower_envs(Tests) ->
    lists:foldl(
        fun(Test, AccEnvs) ->
            TestEnvs = guard_test_lower_envs(Test),
            [{intersect_envs(E1, E2), merge_status(S1, S2)}
             || {E1, S1} <- AccEnvs,
                {E2, S2} <- TestEnvs]
        end,
        [{#{}, safe}],
        Tests).

% Like guard_seq_env/1 but returns a list of disjunctive environments for Lower computation.
% Guard sequences are disjunctive (;) so we concatenate.
-spec guard_seq_lower_envs([ast:guard()]) -> [{constr:constr_env(), safe | unsafe}].
guard_seq_lower_envs([]) -> [{#{}, safe}];
guard_seq_lower_envs(Guards) -> lists:flatmap(fun guard_lower_envs/1, Guards).

% Flips a comparison operator: N op X becomes X flip(op) N.
-spec flip_comparison_op(atom()) -> atom().
flip_comparison_op('>') -> '<';
flip_comparison_op('<') -> '>';
flip_comparison_op('>=') -> '=<';
flip_comparison_op('=<') -> '>='.

% Refinement heuristic for < > <= >= operators and constant types.
% For integer constants, returns an integer range (e.g. X > 2 gives 3..*).
-spec comparison_refine_env(atom(), ast:local_varname(), ast:exp()) -> {constr:constr_env(), safe | unsafe}.
comparison_refine_env(Op, X, ConstExp) ->
    % operators work for any term
    % we can refine only on the integer part
    TyOther = fun(Ty) -> stdtypes:tunion(
                         Ty,
                         ty_without({predef, any}, {predef, integer})
                         ) end,
    case ty_of_const_exp(ConstExp) of
        {ok, {singleton, N}} when is_integer(N) ->
            Ty = case Op of
                '>'  -> TyOther(stdtypes:trange(N + 1, '*'));
                '>=' -> TyOther(stdtypes:trange(N, '*'));
                '<'  -> TyOther(stdtypes:trange('*', N - 1));
                '=<' -> TyOther(stdtypes:trange('*', N))
            end,
            {#{{local_ref, X} => Ty}, safe};
        _ -> {#{}, unsafe}
    end.

% env(g)
-spec guard_seq_env([ast:guard()]) -> {constr:constr_env(), safe | unsafe}.
guard_seq_env(Guards) ->
    combine_guard_result(Guards, fun guard_env/1, fun union_envs/2).

-spec guard_env(ast:guard()) -> {constr:constr_env(), safe | unsafe}.
guard_env(Guards) ->
    combine_guard_result(Guards, fun guard_test_env/1, fun intersect_envs/2).

-spec combine_guard_result(list(G),
                           fun((G) -> {constr:constr_env(), safe | unsafe}),
                           fun((constr:constr_env(), constr:constr_env()) ->
                                      constr:constr_env())) ->
          {constr:constr_env(), safe | unsafe}.
combine_guard_result([], _RecFun, _CombineFun) ->
    {#{}, safe};
combine_guard_result(Guards, RecFun, CombineFun) ->
    [First | Rest] = lists:map(RecFun, Guards),
    lists:foldl(fun({Env, Status}, {AccEnv, AccStatus}) ->
                        {CombineFun(Env, AccEnv), merge_status(Status, AccStatus)}
                end,
                First,
                Rest).

% Constructs an environment and a status from a guard test. The status 'safe' expresses
% that the the type checker could fully analyze the guard, that is the guard test
% does not use anything like the "oracle" from the IFL 2022 paper.
-spec guard_test_env(ast:guard_test()) -> {constr:constr_env(), safe | unsafe}.
guard_test_env(G) ->
    Default = {#{}, unsafe},
    case G of
        {call, _L, FunExp, Args} ->
            % check whether first arg is a variable
            case Args of
                [Fst | Rest] ->
                    case Fst of
                        {var, _, {local_ref, X}} -> var_test_env(FunExp, X, Rest);
                        _ -> Default
                    end;
                _ -> Default
            end;
        {op, _L, Op, Left, Right} ->
            if
                (Op =:= 'andalso') orelse (Op =:= 'and') ->
                    {EnvLeft, StatusLeft} = guard_test_env(Left),
                    {EnvRight, StatusRight} = guard_test_env(Right),
                    {intersect_envs(EnvLeft, EnvRight), merge_status(StatusLeft, StatusRight)};
                (Op =:= 'orelse') orelse (Op =:= 'or') ->
                    {EnvLeft, StatusLeft} = guard_test_env(Left),
                    {EnvRight, StatusRight} = guard_test_env(Right),
                    {union_envs(EnvLeft, EnvRight), merge_status(StatusLeft, StatusRight)};
                (Op =:= '==') orelse (Op =:= '=:=') ->
                    refine_eq_env(Left, Right);
                (Op =:= '>') orelse (Op =:= '<') orelse (Op =:= '>=') orelse (Op =:= '=<') ->
                    case {Left, Right} of
                        {{var, _, {local_ref, X}}, E} -> comparison_refine_env(Op, X, E);
                        {E, {var, _, {local_ref, X}}} -> comparison_refine_env(flip_comparison_op(Op), X, E);
                        _ -> Default
                    end;
                true -> Default
            end;
        {op, _L, 'not', Exp} ->
            {Env, Status} = guard_test_env(Exp),
            {negate_env(Env), Status};
        {'atom', _Loc, true} ->
            {#{}, safe};
        _ -> Default
    end.

% Best-effort recursive refine variable types from an equality guard Left == Right or Left =:= Right.
% Variables in Left are refined to a possibly constant type of the corresponding part of Right, and vice versa.
-spec refine_eq_env(ast:exp(), ast:exp()) -> {constr:constr_env(), safe | unsafe}.
refine_eq_env(Left, Right) ->
    case {Left, Right} of
        {{var, _, {local_ref, X}}, _} ->
            case ty_of_const_exp(Right) of
                {ok, Ty} -> {#{{local_ref, X} => Ty}, safe};
                error -> {#{}, unsafe}
            end;
        {_, {var, _, {local_ref, X}}} ->
            case ty_of_const_exp(Left) of
                {ok, Ty} -> {#{{local_ref, X} => Ty}, safe};
                error -> {#{}, unsafe}
            end;
        {{tuple, _, LeftElems}, {tuple, _, RightElems}}
                when length(LeftElems) =:= length(RightElems) ->
            lists:foldl(
                fun({L, R}, {EnvAcc, StatusAcc}) ->
                    {Env, Status} = refine_eq_env(L, R),
                    {intersect_envs(Env, EnvAcc), merge_status(Status, StatusAcc)}
                end,
                {#{}, safe},
                lists:zip(LeftElems, RightElems));
        _ ->
            % safe if both constant structurally equal
            case {ty_of_const_exp(Left), ty_of_const_exp(Right)} of
                {{ok, T}, {ok, T}} -> {#{}, safe};
                _ -> {#{}, unsafe}
            end
    end.

% Returns the type of a constant (variable-free) expression, or error if not constant.
-spec ty_of_const_exp(ast:exp()) -> t:opt(ast:ty()).
ty_of_const_exp(E) ->
    case E of
        {'atom', _, A} -> {ok, {singleton, A}};
        {'integer', _, I} -> {ok, {singleton, I}};
        {'char', _, C} -> {ok, {singleton, C}};
        {op, _, '-', {'integer', _, I}} -> {ok, {singleton, -I}};
        {tuple, _, Elems} ->
            TysOpt = lists:map(fun ty_of_const_exp/1, Elems),
            case lists:all(fun(R) -> R =/= error end, TysOpt) of
                true -> {ok, {tuple, lists:map(fun({ok, T}) -> T end, TysOpt)}};
                false -> error
            end;
        _ -> error
    end.

merge_status(safe, safe) -> safe;
merge_status(_, _) -> unsafe.

% {var,{loc,"test_files/tycheck_simple.erl",202,16},{qref,erlang,is_integer,1}} for {'Y',0} and args []: {#{},unsafe}
-spec var_test_env(ast:guard_test(), ast:local_varname(), [ast:guard_test()]) ->
          {constr:constr_env(), safe | unsafe}.
var_test_env(FunExp, X, RestArgs) ->
    Default = {#{}, unsafe},
    XRef = {local_ref, X},
    Env =
        case FunExp of
            {var, _, Ref} ->
                case
                    case Ref of
                        {ref, A, B} -> {A, B};
                        {qref, erlang, A, B} -> {A, B};
                        _ -> unsupported
                    end
                of
                    unsupported -> Default;
                    {is_record, Arity} ->
                        % check whether first rest arg is an atom (the record name)
                        if
                            Arity =:= 2 orelse Arity =:= 3 ->
                                case RestArgs of
                                    [{'atom', _, RecordName} | _] ->
                                        {#{XRef => {record, RecordName, []}}, safe};
                                    _ -> Default
                                end;
                            true -> Default
                        end;
                    {is_function, 2} ->
                        case RestArgs of
                            [{'integer', _, N}] ->
                                % The top type for functions with arity N
                                TopFunTy = {fun_full, utils:replicate(N, {predef, none}), {predef, any}},
                                {#{XRef => TopFunTy}, safe};
                            _ -> Default
                        end;
                    {Name, 1} ->
                        case Name of
                            is_atom -> {#{XRef => {predef, atom}}, safe};
                            is_binary -> {#{XRef => {predef_alias, binary}}, safe};
                            is_bitstring -> {#{XRef => {predef_alias, bitstring}}, safe};
                            is_boolean -> {#{XRef => {predef_alias, boolean}}, safe};
                            is_function -> {#{XRef => {predef_alias, function}}, safe};
                            is_integer -> {#{XRef => {predef, integer}}, safe};
                            is_float -> {#{XRef => {predef, float}}, safe};
                            is_list -> {#{XRef => {predef_alias, list}}, safe};
                            is_map -> {#{XRef => {predef_alias, map}}, safe};
                            is_number -> {#{XRef => {predef_alias, number}}, safe};
                            is_pid -> {#{XRef => {predef, pid}}, safe};
                            is_port -> {#{XRef => {predef, port}}, safe};
                            is_reference -> {#{XRef => {predef, reference}}, safe};
                            is_tuple -> {#{XRef => {tuple_any}}, safe};
                            _ ->
                                case string:prefix(atom_to_list(Name), "is_") of
                                    nomatch -> ok;
                                    _ -> ?LOG_INFO("Unsupported type test ~w", Name)
                                end,
                                Default
                        end
                end;
            _ ->
                Default
        end,
    ?LOG_TRACE("Env resulting from var test ~200p for ~w and args ~200p: ~w", FunExp, X, RestArgs, Env),
    Env.


% f(p11, p12, ..., p1n) -> e1;
% ...
% f(pm1, pm2, ..., pmn) -> em
%
% is transformed into
%
% case {X1, ..., Xn} of
%   (p11, p12, ..., p1n) -> e1;
%   ...
%   (pm1, pm2, ..., pmn) -> em
% end
-spec fun_clauses_to_exp(ctx(), ast:loc(), [ast:fun_clause()]) -> {[ast:local_varname()], ast:exps()}.
fun_clauses_to_exp(Ctx, _, FunClauses = [{fun_clause, L, Pats, [], Body}]) ->
    % special case: only one clause, no guards, all patterns are variables
    Vars =
        lists:foldr(fun (Pat, Acc) ->
                            case {Acc, Pat} of
                                {error, _} -> error;
                                {Vars, {var, _, {local_bind, V}}} -> [V | Vars];
                                _ -> error
                            end
                    end, [], Pats),
    case Vars of
        error -> fun_clauses_to_exp_aux(Ctx, L, FunClauses);
        VarList -> {VarList, Body}
    end;
fun_clauses_to_exp(Ctx, L, FunClauses) ->
    fun_clauses_to_exp_aux(Ctx, L, FunClauses).

-spec fun_clauses_to_exp_aux(ctx(), ast:loc(), [ast:fun_clause()]) -> {[ast:local_varname()], ast:exps()}.
fun_clauses_to_exp_aux(Ctx, L, FunClauses) ->
    Arity =
        case FunClauses of
            [] -> errors:ty_error(L, "expected function clauses");
            [{fun_clause, _, FirstPats, _, _} | Rest] ->
                lists:foldl(
                  fun({fun_clause, ThisLoc, ThisPats, _, _}, Arity) ->
                          if
                              length(ThisPats) =:= Arity -> Arity;
                              true -> errors:ty_error(ThisLoc,
                                                      "expected ~w arguments, but given ~w",
                                                      [Arity, length(ThisPats)])
                          end
                  end,
                  length(FirstPats),
                  Rest)
        end,
    Vars = fresh_vars(Ctx, Arity),
    ScrutExp = {tuple, L, lists:map(fun(V) -> {var, L, {local_ref, V}} end, Vars)},
    CaseClauses = lists:map(fun fun_clause_to_case_clause/1, FunClauses),
    E = {'case', L, ScrutExp, CaseClauses},
    ?LOG_TRACE("Rewrote function clauses at ~s with arguments=~w:\n~200p", ast:format_loc(L), Vars, E),
    {Vars, [E]}.

-spec fun_clause_to_case_clause(ast:fun_clause()) -> ast:case_clause().
fun_clause_to_case_clause({fun_clause, L, Pats, Guards, Exps}) ->
    {case_clause, L, {tuple, L, Pats}, Guards, Exps}.

% if g1 -> e1;
%    ...
%    gn -> en
% end
%
% is transformed to
%
% case {}
%   _ when g1 -> e1;
%   ...
%   _ when gn -> en
% end
-spec if_exp_to_case_exp(ast:exp_if()) -> ast:exp_case().
if_exp_to_case_exp({'if', L, IfClauses}) ->
    ScrutExp = {tuple, L, []},
    Pat = {wildcard, L},
    CaseClauses =
        lists:map(fun({if_clause, ClauseLoc, Guards, Body}) ->
                          {case_clause, ClauseLoc, Pat, Guards, Body}
                  end, IfClauses),
    {'case', L, ScrutExp, CaseClauses}.

-spec sanity_check(constr:constrs(), ast_check:ty_map()) -> ok.
sanity_check(Cs, Spec) ->
    case ast_check:check_against_type(Spec, constr, constrs, Cs) of
        true ->
            ?LOG_DEBUG("Sanity check OK"),
            ok;
        false ->
            ?ABORT("Sanity check failed: ~s", "invalid constraint generated")
    end.

-spec is_exhaustiveness_disabled_for_fun(atom(), arity(), feature_flags:exhaustiveness_mode(), sets:set({atom(), arity()})) -> feature_flags:exhaustiveness_mode().
is_exhaustiveness_disabled_for_fun(Name, Arity, ExhaustivenessMode, DisableExhaustiveness) ->
    case sets:is_element({Name, Arity}, DisableExhaustiveness) of
        true -> disabled;
        _ -> ExhaustivenessMode
    end.
