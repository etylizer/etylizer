-module(constr_gen).

-include_lib("log.hrl").

-export([
         gen_constrs_fun_group/2, gen_constrs_annotated_fun/3,
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
          symtab :: symtab:t()
        }).
-type ctx() :: #ctx{}.

-spec new_ctx(symtab:t()) -> ctx().
new_ctx(Symtab) ->
    Counter = counters:new(2, []),
    Ctx = #ctx{ var_counter = Counter, symtab = Symtab },
    Ctx.

-spec fresh_tyvar(ctx()) -> ast:ty_var().
fresh_tyvar(Ctx) ->
    I = counters:get(Ctx#ctx.var_counter, 1),
    counters:add(Ctx#ctx.var_counter, 1, 1),
    S = utils:sformat("$~w", I),
    {var, list_to_atom(S)}.

-spec fresh_vars(ctx(), arity()) -> [ast:local_varname()].
fresh_vars(Ctx, N) ->
    I = counters:get(Ctx#ctx.var_counter, 2),
    counters:add(Ctx#ctx.var_counter, 2, 1),
    Loop =
        fun Loop(J) ->
                if
                    J > N -> [];
                    true ->
                        ArgJ = list_to_atom(utils:sformat("A~w", J)),
                        X = {ArgJ, I},
                        [X | Loop(J + 1)]
                end
        end,
    Loop(1).

-spec mk_locs(string(), ast:loc()) -> constr:locs().
mk_locs(Label, X) -> {Label, utils:single(X)}.

% Inference for a group of mutually recursive functions without type annotations.
-spec gen_constrs_fun_group(symtab:t(), [ast:fun_decl()]) -> {constr:constrs(), constr:constr_env()}.
gen_constrs_fun_group(Symtab, Decls) ->
    Ctx = new_ctx(Symtab),
    lists:foldl(
      fun({function, L, Name, Arity, FunClauses}, {Cs, Env}) ->
              Exp = {'fun', L, no_name, FunClauses},
              Alpha = fresh_tyvar(Ctx),
              ThisCs = exp_constrs(Ctx, Exp, Alpha),
              Ref = {ref, Name, Arity},
              {sets:union(ThisCs, Cs), maps:put(Ref, Alpha, Env)}
      end, {sets:new(), #{}}, Decls).

% Checking the type spec of a function.
% This function is invoked for each branch of the intersection type in the type spec.
% The idea is that we can give better error messages by pointing out which part of the
% intersection did not type check.
-spec gen_constrs_annotated_fun(symtab:t(), ast:ty_full_fun(), ast:fun_decl()) -> constr:constrs().
gen_constrs_annotated_fun(Symtab, {fun_full, ArgTys, ResTy}, {function, L, Name, Arity, FunClauses}) ->
    Ctx = new_ctx(Symtab),
    {Args, Body} = fun_clauses_to_exp(Ctx, L, FunClauses),
    if length(Args) =/= length(ArgTys) orelse length(Args) =/= Arity ->
            errors:ty_error(L, "Arity mismatch for function ~w", Name);
       true -> ok
    end,
    ArgRefs = lists:map(fun(V) -> {local_ref, V} end, Args),
    Env = maps:from_list(lists:zip(ArgRefs, ArgTys)),
    BodyCs = exps_constrs(Ctx, L, Body, ResTy),
    Msg = utils:sformat("definition of ~w/~w", Name, Arity),
    utils:single({cdef, mk_locs(Msg, L), Env, BodyCs}).

-spec exps_constrs(ctx(), ast:loc(), [ast:exp()], ast:ty()) -> constr:constrs().
exps_constrs(Ctx, _L, Es, T) ->
    case lists:reverse(Es) of
        [] -> ?ABORT("empty list of expressions");
        [Last | Init] ->
            Cs0 = exp_constrs(Ctx, Last, T),
            lists:foldl(fun (E, Acc) ->
                                Alpha = fresh_tyvar(Ctx),
                                Cs = exp_constrs(Ctx, E, Alpha),
                                % Question: Constraint Alpha to unit?
                                sets:union(Acc, Cs)
                        end,
                        Cs0,
                        Init)
    end.

-spec exp_constrs(ctx(), ast:exp(), ast:ty()) -> constr:constrs().
exp_constrs(Ctx, E, T) ->
    case E of
        {'atom', L, A} -> utils:single({csubty, mk_locs("atom literal", L), {singleton, A}, T});
        {'char', L, C} -> utils:single({csubty, mk_locs("char literal", L), {singleton, C}, T});
        {'integer', L, I} -> utils:single({csubty, mk_locs("int literal", L), {singleton, I}, T});
        {'float', L, _F} -> utils:single({csubty, mk_locs("float literal", L), {predef, float}, T});
        {'string', L, ""} -> utils:single({csubty, mk_locs("empty string literal", L), {empty_list}, T});
        {'string', L, _S} -> utils:single({csubty, mk_locs("string literal", L), {predef_alias, string}, T});
        {bc, L, _E, _Qs} -> errors:unsupported(L, "bitstrings");
        {block, L, Es} -> exps_constrs(Ctx, L, Es, T);
        {'case', L, ScrutE, Clauses} ->
            Alpha = fresh_tyvar(Ctx),
            Cs0 = exp_constrs(Ctx, ScrutE, Alpha),
            NeedsUnmatchedCheck = needs_unmatched_check(Clauses),
            {BodyList, Lowers, _Uppers, CsCases} =
                lists:foldl(fun (Clause = {case_clause, LocClause, _, _, _},
                                 {BodyList, Lowers, Uppers, AccCs}) ->
                                    ?LOG_TRACE("Generating constraint for case clause at ~s: Lowers=~s, Uppers=~s",
                                               ast:format_loc(LocClause),
                                               pretty:render_tys(Lowers),
                                               pretty:render_tys(Uppers)),
                                    {ThisLower, ThisUpper, ThisCs, ThisConstrBody} =
                                        case_clause_constrs(
                                          Ctx,
                                          ty_without(Alpha, ast_lib:mk_union(Lowers)),
                                          ScrutE,
                                          NeedsUnmatchedCheck,
                                          Lowers,
                                          Clause,
                                          T),
                                    {BodyList ++ [ThisConstrBody],
                                     Lowers ++ [ThisLower],
                                     Uppers ++ [ThisUpper],
                                     sets:union(ThisCs, AccCs)}
                            end,
                            {[], [], [], sets:new()},
                            Clauses),
            CsScrut = sets:union(Cs0, CsCases),
            Exhaust = utils:single(
                {csubty, mk_locs("case exhaustiveness", L), Alpha, ast_lib:mk_union(Lowers)}),
            sets:from_list([
                {ccase, mk_locs("case", L), CsScrut, Exhaust, BodyList}
            ]);
        {'catch', L, CatchE} ->
            Top = {predef, any},
            Cs = exp_constrs(Ctx, CatchE, Top),
            sets:add_element({csubty, mk_locs("result of catch", L), Top, T}, Cs);
        {cons, L, Head, Tail} ->
            Alpha = fresh_tyvar(Ctx),
            CsHead = exp_constrs(Ctx, Head, Alpha),
            CsTail = exp_constrs(Ctx, Tail, T),
            sets:add_element({csubty, mk_locs("result of cons", L), {list, Alpha}, T},
                             sets:union(CsHead, CsTail));
        {fun_ref, L, GlobalRef} ->
            utils:single({cvar, mk_locs("function ref", L), GlobalRef, T});
        {'fun', L, RecName, FunClauses} ->
            {Args, BodyExps} = fun_clauses_to_exp(Ctx, L, FunClauses),
            ArgTys = lists:map(fun(X) -> {{local_ref, X}, fresh_tyvar(Ctx)} end, Args),
            ArgEnv = maps:from_list(ArgTys),
            ResTy = fresh_tyvar(Ctx),
            FunTy = {fun_full, lists:map(fun({_, Ty}) -> Ty end, ArgTys), ResTy},
            CsBody = exps_constrs(Ctx, L, BodyExps, ResTy),
            BodyEnv =
                case RecName of
                    no_name -> ArgEnv;
                    {local_bind, F} -> maps:put({local_ref, F}, FunTy, ArgEnv)
                end,
            sets:from_list([{cdef, mk_locs("function def", L), BodyEnv, CsBody},
                            {csubty, mk_locs("result of fun exp", L), FunTy, T}]);
        {call, L, FunExp, Args} ->
            {ArgCs, ArgTys} =
                lists:foldr(
                  fun(ArgExp, {AccCs, AccTys}) ->
                          Alpha = fresh_tyvar(Ctx),
                          Cs = exp_constrs(Ctx, ArgExp, Alpha),
                          {sets:union(AccCs, Cs), [Alpha | AccTys]}
                  end,
                  {sets:new(), []},
                  Args),
            Beta = fresh_tyvar(Ctx),
            FunTy = {fun_full, ArgTys, Beta},
            FunCs = exp_constrs(Ctx, FunExp, FunTy),
            Description =
                case FunExp of
                    {var, _, AnyRef} ->
                        "result of calling " ++ pretty:render_any_ref(AnyRef);
                    _ -> "result of function call"
                end,
            sets:add_element(
              {csubty, mk_locs(Description, L), Beta, T},
              sets:union(FunCs, ArgCs));
        {call_remote, L, _ModExp, _FunExp, _Args} ->
            errors:unsupported(L, "function calls with dynamically computed modules");
        ({'if', _, _} = IfExp) ->
            exp_constrs(Ctx, if_exp_to_case_exp(IfExp), T);
        {lc, L, _E, _Qs} ->
            errors:unsupported(L, "list comprehension: ~200p", [E]);
        {map_create, L, Assocs} ->
            KeyAlpha = fresh_tyvar(Ctx),
            ValAlpha = fresh_tyvar(Ctx),
            MapTy = {map, [{map_field_opt, KeyAlpha, ValAlpha}]},
            AssocsCs =
                lists:foldl(
                  fun({map_field_opt, _FieldL, KeyE, ValE}, AccCs) ->
                          KeyCs = exp_constrs(Ctx, KeyE, KeyAlpha),
                          ValCs = exp_constrs(Ctx, ValE, ValAlpha),
                          sets:union([AccCs, KeyCs, ValCs])
                  end,
                  sets:new(),
                  Assocs),
            ResultC = {csubty, mk_locs("map_create", L), MapTy, T},
            sets:add_element(ResultC, AssocsCs);
        {map_update, L, MapExp, Assocs} ->
            KeyAlpha = fresh_tyvar(Ctx),
            ValAlpha = fresh_tyvar(Ctx),
            MapTy = {map, [{map_field_opt, KeyAlpha, ValAlpha}]},
            Cs1 = exp_constrs(Ctx, MapExp, MapTy),
            Cs2 =
                lists:foldl(
                fun(Assoc, AccCs) ->
                    {KeyE, ValE} =
                        case Assoc of
                            {map_field_opt, _FieldL, K, V} -> {K, V};
                            {map_field_req, _FieldL, K, V} -> {K, V}
                        end,
                    KeyCs = exp_constrs(Ctx, KeyE, KeyAlpha),
                    ValCs = exp_constrs(Ctx, ValE, ValAlpha),
                    sets:union([AccCs, KeyCs, ValCs])
                end,
                Cs1,
                Assocs),
            ResultC = {csubty, mk_locs("map_update", L), MapTy, T},
            sets:add_element(ResultC, Cs2);
        {nil, L} ->
            utils:single({csubty, mk_locs("result of nil", L), {empty_list}, T});
        {op, L, Op, Lhs, Rhs} ->
            Alpha1 = fresh_tyvar(Ctx),
            Cs1 = exp_constrs(Ctx, Lhs, Alpha1),
            Alpha2 = fresh_tyvar(Ctx),
            Cs2 = exp_constrs(Ctx, Rhs, Alpha2),
            Beta = fresh_tyvar(Ctx),
            MsgTy = utils:sformat("type of op ~w", Op),
            MsgRes = utils:sformat("result of op ~w", Op),
            OpCs = sets:from_list(
                     [{cop, mk_locs(MsgTy, L), Op, 2, {fun_full, [Alpha1, Alpha2], Beta}},
                      {csubty, mk_locs(MsgRes, L), Beta, T}]),
            sets:union([Cs1, Cs2, OpCs]);
        {op, L, Op, Arg} ->
            Alpha = fresh_tyvar(Ctx),
            ArgCs = exp_constrs(Ctx, Arg, Alpha),
            Beta = fresh_tyvar(Ctx),
            MsgTy = utils:sformat("type of op ~w", Op),
            MsgRes = utils:sformat("result of op ~w", Op),
            OpCs = sets:from_list(
                     [{cop, mk_locs(MsgTy, L), Op, 1, {fun_full, [Alpha], Beta}},
                      {csubty, mk_locs(MsgRes, L), Beta, T}]),
            sets:union(ArgCs, OpCs);
        {'receive', L, _CaseClauses} ->
            errors:unsupported(L, "receive: ~200p", [E]);
        {receive_after, L, _CauseClauses, _TimeoutExp, _Body} ->
            errors:unsupported(L, "receive_after: ~200p", [E]);
        {record_create, L, Name, GivenFields} ->
            {_, DefFields} = symtab:lookup_record(Name, L, Ctx#ctx.symtab),
            VarFields =
                lists:map(
                    fun ({N, _}) ->
                        Alpha = fresh_tyvar(Ctx),
                        {N, Alpha}
                    end,
                    DefFields),
            DefFieldNames = sets:from_list(lists:map(fun ({N, _}) -> N end, DefFields)),
            GivenFieldNames =
                sets:from_list(lists:map(fun ({record_field, _L, N, _Exp}) -> N end, GivenFields)),
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
                        ThisCs = exp_constrs(Ctx, Exp, Ty),
                        sets:union(Cs, ThisCs)
                    end,
                    sets:new(),
                    GivenFields),
            RecTupleTy = records:encode_record_ty({Name, VarFields}),
            RecConstr = {csubty, mk_locs("record value constructor", L), RecTupleTy, T},
            sets:add_element(RecConstr, Cs);
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
            Cs = exp_constrs(Ctx, Exp, RecTupleTy),
            FieldConstr = {csubty, mk_locs("record field access", L), Alpha, T},
            sets:add_element(FieldConstr, Cs);
        {record_index, L, RecName, FieldName} ->
            RecTy = symtab:lookup_record(RecName, L, Ctx#ctx.symtab),
            {_FieldTy, Idx} = records:lookup_field_index(RecTy, FieldName, L),
            Constr = {csubty, mk_locs("record field index", L), stdtypes:tint(Idx + 1), T},
            utils:single(Constr);
        {record_update, L, Exp, RecName, FieldUpdates} ->
            {_, DefFields} = symtab:lookup_record(RecName, L, Ctx#ctx.symtab),
            UpdatedFieldNames =
                sets:from_list(
                    lists:map(fun({record_field, _, FieldName, _}) -> FieldName end, FieldUpdates)
                ),
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
            ExpCs = exp_constrs(Ctx, Exp, RecTupleTyExp),
            FieldsForRes = lists:map(fun ({N, _, Ty}) -> {N, Ty} end, FieldTypes),
            RecTyRes = {RecName, FieldsForRes},
            RecTupleTyRes = records:encode_record_ty(RecTyRes),
            ResConstr = {csubty, mk_locs("record result", L), RecTupleTyRes, T},
            lists:foldr(
                fun({record_field, FieldUpdateLoc, FieldName, FieldExp}, Cs) ->
                    FieldTy = records:lookup_field_ty(RecTyRes, FieldName, FieldUpdateLoc),
                    ThisCs = exp_constrs(Ctx, FieldExp, FieldTy),
                    sets:union(Cs, ThisCs)
                end,
                sets:add_element(ResConstr, ExpCs),
                FieldUpdates);
        {tuple, L, Args} ->
            {Tys, Cs} =
                lists:foldr(
                  fun(Arg, {Tys, Cs}) ->
                          Alpha = fresh_tyvar(Ctx),
                          ThisCs = exp_constrs(Ctx, Arg, Alpha),
                          {[Alpha | Tys], sets:union(Cs, ThisCs)}
                  end,
                  {[], sets:new()},
                  Args),
            TupleC = {csubty, mk_locs("tuple constructor", L), {tuple, Tys}, T},
            sets:add_element(TupleC, Cs);
        {'try', L, _Exps, _CaseClauses, _CatchClauses, _AfterBody} ->
            errors:unsupported(L, "try: ~200p", [E]);
        {var, L, AnyRef} ->
            Msg = utils:sformat("var ~s", pretty:render(pretty:ref(AnyRef))),
            utils:single({cvar, mk_locs(Msg, L), AnyRef, T});
        X -> errors:uncovered_case(?FILE, ?LINE, X)
    end.

-spec ty_without(ast:ty(), ast:ty()) -> ast:ty().
ty_without(T1, T2) -> ast_lib:mk_intersection([T1, ast_lib:mk_negation(T2)]).

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
    exp_constrs(Ctx, Scrut, Ui).

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
    ctx(), ast:ty(), ast:exp(), boolean(), list(ast:ty()), ast:case_clause(), ast:ty()
) -> {ast:ty(), ast:ty(), constr:constrs(), constr:constr_case_branch()}.
case_clause_constrs(Ctx, TyScrut, Scrut, NeedsUnmatchedCheck, LowersBefore,
    {case_clause, L, Pat, Guards, Exps}, ExpectedTy) ->
    {BodyLower, BodyUpper, BodyEnvCs, BodyEnv} =
        case_clause_env(Ctx, L, TyScrut, Scrut, Pat, Guards),
    {_, _, GuardEnvCs, GuardEnv} = case_clause_env(Ctx, L, TyScrut, Scrut, Pat, []),
    ?LOG_TRACE("TyScrut=~w, Scrut=~w, GuardEnv=~w, BodyEnv=~w", TyScrut, Scrut, GuardEnv, BodyEnv),
    Beta = fresh_tyvar(Ctx),
    InnerCs = exps_constrs(Ctx, L, Exps, Beta),
    CGuards =
        sets:union(
          lists:map(
            fun(Guard) ->
                    exps_constrs(Ctx, L, Guard, {predef_alias, boolean})
            end,
            Guards)),
    RedundancyCs =
        if
            NeedsUnmatchedCheck ->
                case_clause_unmatched_constraints(Ctx, LowersBefore, BodyUpper, Scrut);
            true -> none
        end,
    RL =
        case Exps of
            [] -> L;
            [E | _] -> ast:loc_exp(E)
        end,
    ResultLocs = mk_locs("case result", RL),
    ResultCs = utils:single({csubty, ResultLocs, Beta, ExpectedTy}),
    Payload = constr:mk_case_branch_payload(
        {GuardEnv, CGuards}, {BodyEnv, InnerCs}, RedundancyCs, ResultCs),
    ConstrBody = {ccase_branch, mk_locs("case branch", L), Payload},
    AllCs = sets:union([BodyEnvCs, GuardEnvCs]),
    {BodyLower, BodyUpper, AllCs, ConstrBody}.

% helper function for case_clause_constrs
-spec case_clause_env(ctx(), ast:loc(), ast:ty(), ast:exp(), ast:pat(), [ast:guard()]) ->
          {ast:ty(), ast:ty(), constr:constrs(), symtab:fun_env()}.
case_clause_env(Ctx, L, TyScrut, Scrut, Pat, Guards) ->
    {Lower, Upper} = pat_guard_lower_upper(Ctx#ctx.symtab, Pat, Guards, Scrut),
    Ti = ast_lib:mk_intersection([TyScrut, Upper]),
    {Ci0, Gamma0} = pat_env(Ctx, L, Ti, pat_of_exp(Scrut)),
    {Ci1, Gamma1} = pat_guard_env(Ctx, L, Ti, Pat, Guards),
    Gamma2 = intersect_envs(Gamma1, Gamma0),
    {Lower, Upper, sets:union(Ci0, Ci1), Gamma2}.

% ⌊ p when g ⌋_e and ⌈ p when g ⌉_e
-spec pat_guard_lower_upper(symtab:t(), ast:pat(), [ast:guard()], ast:exp()) -> {ast:ty(), ast:ty()}.
pat_guard_lower_upper(Symtab, P, Gs, E) ->
    % Env has type constr:constr_env() = #{ast:any_ref() => ast:ty()}
    {Env, Status} = guard_seq_env(Gs),
    EPat = pat_of_exp(E),
    UpperPatTy = ty_of_pat(Symtab, Env, P, upper),
    LowerPatTy = ty_of_pat(Symtab, Env, P, lower),
    UpperETy = ty_of_pat(Symtab, Env, EPat, upper),
    LowerETy = ty_of_pat(Symtab, Env, EPat, lower),
    Upper = ast_lib:mk_intersection([UpperPatTy, UpperETy]),
    VarsOfGuards = sets:from_list(lists:filtermap(fun ast:local_varname_from_any_ref/1, maps:keys(Env))),
    BoundVars = sets:union(bound_vars_pat(P), bound_vars_pat(EPat)),
    Lower =
        case {Status, sets:is_subset(VarsOfGuards, BoundVars)} of
            {safe, true} -> ast_lib:mk_intersection([LowerPatTy, LowerETy]);
            _ -> {predef, none}
        end,
    ?LOG_TRACE("EPat=~200p, UpperPatTy=~s, LowerPatTy=~s, UpperETy=~s, LowerETy=~s Upper=~s, Lower=~s, VarsOfGuards=~200p, BoundVars=~w, Status=~w",
               EPat,
               pretty:render_ty(UpperPatTy),
               pretty:render_ty(LowerPatTy),
               pretty:render_ty(UpperETy),
               pretty:render_ty(LowerETy),
               pretty:render_ty(Upper),
               pretty:render_ty(Lower),
               maps:keys(Env),
               sets:to_list(BoundVars),
               Status),
    {Lower, Upper}.

% The variables bound by a pattern
-spec bound_vars_pat(ast:pat()) -> sets:set(ast:local_varname()).
bound_vars_pat(P) ->
    case P of
        {'atom', _L, _A} -> sets:new();
        {'char', _L, _C} -> sets:new();
        {'integer', _L, _I} -> sets:new();
        {'float', _L, _F} -> sets:new();
        {'string', _L, _S} -> sets:new();
        {bin, L, _Elems} -> errors:unsupported(L, "bitstring patterns");
        {match, _L, P1, P2} ->
            sets:union(bound_vars_pat(P1), bound_vars_pat(P2));
        {nil, _L} -> sets:new();
        {cons, _L, P1, P2} ->
            sets:union(bound_vars_pat(P1), bound_vars_pat(P2));
        {op, _L, _Op, Ps} ->
            lists:foldl(
              fun(P, Acc) -> sets:union(Acc, bound_vars_pat(P)) end,
              sets:new(),
              Ps
             );
        {map, _L, Assocs} ->
            lists:foldl(
              % NOTE: the key part of a map pattern does not bound variables
              fun({map_field_req, _L, _P1, P2}, Acc) -> sets:union(Acc, bound_vars_pat(P2)) end,
              sets:new(),
              Assocs
             );
        {record, _L, _RecName, FieldPatterns} ->
            lists:foldl(
              fun({record_field, _L, _FieldName, P}, Acc) -> sets:union(Acc, bound_vars_pat(P)) end,
              sets:new(),
              FieldPatterns
             );
        {record_index, _L, _Name, _Field} -> sets:new();
        {tuple, _L, Ps} ->
            lists:foldl(
              fun(P, Acc) -> sets:union(Acc, bound_vars_pat(P)) end,
              sets:new(),
              Ps
             );
        {wildcard, _L} -> sets:new();
        {var, _L, {local_bind, V}} -> sets:from_list([V]);
        {var, _L, {local_ref, _V}} -> sets:new()
    end.


% ty_of_pat
% \lbag p \rbag_\Gamma
%
% In the paper, the type t of a pattern p has the following semantics:
%     Expression e matches p if, and only if, e has type t
%
% With list patterns, this is no longer true.
%
% Example 1: pattern [1 | _].
% For the => direction above, consider an expression e that matches
% this pattern. From this, all we know is that e must have type nonempty_list(any()).
% (e could be any of the following expressions: [1,2,3] or [1, "foo"] or [1]).
% For the <= direction, e must have type nonempty_list(1) if we want to make sure
% that the pattern definitely matches.
% Example 2: pattern [_ | _ | _].
% For the => direction, consider an expression e that matches the pattern.
% From this, all we know is that e has type nonempy_list() because there is no
% type for lists with at least length two.
% For the <= direction, no type except none() guarantees that e matches the pattern.
%
% Hence, we introduce a mode for ty_of_pat, which can be either upper or lower.
%
% - Mode upper deals with the potential type. Any expression matching p must
%   be of this type.
%   Example 1: the potential type is nonempty_list(any()).
%   Example 2: the potential type is nonempty_list(any()).
%
% - Mode lower deals with the accepting type. If e has this type, then p definitely
%   matches.
%   Example 1: the accepting type is nonempty_list(1).
%   Example 2: the accepting type is none()
-spec ty_of_pat(symtab:t(), constr:constr_env(), ast:pat(), upper | lower) -> ast:ty().
ty_of_pat(Symtab, Env, P, Mode) ->
    case P of
        {'atom', _L, A} -> {singleton, A};
        {'char', _L, C} -> {singleton, C};
        {'integer', _L, I} -> {singleton, I};
        {'float', _L, _F} -> {predef, float};
        {'string', _L, _S} -> {predef_alias, string};
        {bin, L, _Elems} -> errors:unsupported(L, "bitstring patterns");
        {match, _L, P1, P2} ->
            ast_lib:mk_intersection([ty_of_pat(Symtab, Env, P1, Mode), ty_of_pat(Symtab, Env, P2, Mode)]);
        {nil, _L} -> {empty_list};
        {cons, _L, P1, P2} ->
            case Mode of
                upper ->
                    T1 = ty_of_pat(Symtab, Env, P1, Mode),
                    T2 = ty_of_pat(Symtab, Env, P2, Mode),
                    case subty:is_subty(Symtab, T2, stdtypes:tempty_list()) of
                        true -> stdtypes:tnonempty_list(T1);
                        false ->
                            case subty:is_subty(Symtab, T2, stdtypes:tnonempty_list()) of
                                true -> ast_lib:mk_union([stdtypes:tnonempty_list(T1), T2]);
                                false ->
                                    case subty:is_any(T2, Symtab) of
                                        true -> stdtypes:tnonempty_list();
                                        false -> stdtypes:tnonempty_improper_list(T1, T2)
                                    end
                            end
                    end;
                lower ->
                    T1 = {nonempty_list, ty_of_pat(Symtab, Env, P1, Mode)},
                    T2 = ty_of_pat(Symtab, Env, P2, Mode),
                    % FIXME: can we encode this choice as a type?
                    case subty:is_any(T2, Symtab) of
                        true -> T1;
                        false -> stdtypes:empty()
                    end
            end;
        {op, _, '++', [P1, P2]} ->
            ast_lib:mk_intersection([ty_of_pat(Symtab, Env, P1, Mode), ty_of_pat(Symtab, Env, P2, Mode),
                                 {predef_alias, string}]);
        {op, _, '-', [SubP]} ->
            ast_lib:mk_intersection([ty_of_pat(Symtab, Env, SubP, Mode), {predef_alias, number}]);
        {op, L, Op, _} -> errors:unsupported(L, "operator ~w in patterns", Op);
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
            stdtypes:tmap(F(KeyTs), F(ValTs));
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
        {var, _L, {local_bind, V}} -> maps:get({local_ref, V}, Env, {predef, any});
        {var, _L, {local_ref, _V}} -> {predef, any} % we could probably do better here
    end.

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
    Empty = {sets:new(), #{}},
    case P of
        {'atom', _L, _A} -> Empty;
        {'char', _L, _C} -> Empty;
        {'integer', _L, _I} -> Empty;
        {'float', _L, _F} -> Empty;
        {'string', _L, _S} -> Empty;
        {bin, L, _Elems} -> errors:unsupported(L, "bitstring patterns");
        {match, _L, P1, P2} ->
            {Cs1, Env1} = pat_env(Ctx, OuterL, T, P1),
            {Cs2, Env2} = pat_env(Ctx, OuterL, T, P2),
            {sets:union(Cs1, Cs2), intersect_envs(Env1, Env2)};
        {nil, _L} ->
            Empty;
        {cons, _L, P1, P2} ->
            Alpha1 = fresh_tyvar(Ctx),
            Alpha2 = fresh_tyvar(Ctx),
            {Cs1, Env1} = pat_env(Ctx, OuterL, Alpha1, P1),
            {Cs2, Env2} = pat_env(Ctx, OuterL, Alpha2, P2),
            C1 = {csubty, mk_locs("t // [_ | _]", OuterL), T, {list, Alpha1}},
            C2 = {csubty, mk_locs("t // [_ | _]", OuterL), T, Alpha2},
            {sets:add_element(C1, sets:add_element(C2, sets:union(Cs1, Cs2))),
             intersect_envs(Env1, Env2)};
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
                    {sets:new(), #{}},
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
                    {sets:new(), #{}, #{}},
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
                          Alpha = fresh_tyvar(Ctx),
                          {ThisCs, ThisEnv} = pat_env(Ctx, OuterL, Alpha, P),
                          {Alphas ++ [Alpha],
                           sets:union(Cs, ThisCs),
                           intersect_envs(Env, ThisEnv)}
                  end,
                  {[], sets:new(), #{}},
                  Ps),
            C = {csubty, mk_locs("t // {...}", OuterL), T, {tuple, Alphas}},
            {sets:add_element(C, Cs), Env};
        {wildcard, _L} ->
            Empty;
        {var, _L, {local_bind, V}} ->
            {sets:new(), #{ {local_ref, V} => T }};
        {var, _L, {local_ref, V}} ->
            {sets:new(), #{ {local_ref, V} => T }}
    end.

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

% Γ //\\ Γ
-spec intersect_envs(constr:constr_env(), constr:constr_env()) -> constr:constr_env().
intersect_envs(Env1, Env2) ->
    combine_envs(Env1, Env2, fun(T1, T2) -> ast_lib:mk_intersection([T1, T2]) end).

-spec combine_envs(
        constr:constr_env(),
        constr:constr_env(),
        fun((ast:ty(), ast:ty()) -> ast:ty())
       ) -> constr:constr_env().
combine_envs(Env1, Env2, F) ->
    Keys = sets:from_list(maps:keys(Env1) ++ maps:keys(Env2)),
    sets:fold(
      fun (K, Env) ->
              T1 = maps:get(K, Env1, none),
              T2 = maps:get(K, Env2, none),
              T = case {T1, T2} of
                      {none, X}-> X;
                      {X, none} -> X;
                      _ -> F(T1, T2)
                  end,
              maps:put(K, T, Env)
      end,
      #{},
      Keys
     ).

% Γ \\// Γ
-spec union_envs(constr:constr_env(), constr:constr_env()) -> constr:constr_env().
union_envs(Env1, Env2) ->
    combine_envs(Env1, Env2, fun(T1, T2) -> ast_lib:mk_union([T1, T2]) end).

-spec negate_env(constr:constr_env()) -> constr:constr_env().
negate_env(Env) -> maps:map(fun (_Key, T) -> ast_lib:mk_negation(T) end, Env).

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
combine_guard_result(Guards, RecFun, CombineFun) ->
    lists:foldl(fun({Env, Status}, {AccEnv, AccStatus}) ->
                        {CombineFun(Env, AccEnv), merge_status(Status, AccStatus)}
                end,
                {#{}, safe},
                lists:map(RecFun, Guards)).

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
                true -> Default
            end;
        {op, _L, 'not', Exp} ->
            {Env, Status} = guard_test_env(Exp),
            {negate_env(Env), Status};
        {'atom', _Loc, true} ->
            {#{}, safe};
        _ -> Default
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
                                TopFunTy = {fun_full, utils:replicate(N, {predef, any}), {predef, none}},
                                {#{XRef => TopFunTy}, safe};
                            _ -> Default
                        end;
                    {Name, 1} ->
                        case Name of
                            is_atom -> {#{XRef => {predef, atom}}, safe};
                            is_binary -> {#{XRef => {predef_alias, binary}}, safe};
                            is_bitstring -> {#{XRef => {predef_alias, bitstring}}, safe};
                            is_function -> {#{XRef => {predef_alias, function}}, safe};
                            is_integer -> {#{XRef => {predef, integer}}, safe};
                            is_float -> {#{XRef => {predef, float}}, safe};
                            is_list -> {#{XRef => {predef_alias, list}}, safe};
                            is_map -> {#{XRef => {predef_alias, map}}, safe};
                            is_number -> {#{XRef => {predef_alias, number}}, safe};
                            is_pid -> {#{XRef => {predef, pid}}, safe};
                            is_port -> {#{XRef => {predef, port}}, safe};
                            is_reference -> {#{XRef => {predef, reference}}, safe};
                            is_tuple -> #{XRef => {tuple_any}};
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
