-module(typing).

-export([
    check_forms/6, check_forms/7,
    new_ctx/3,
    new_ctx/7,
    resolve_disabled_funs/2,
    recv_msg_tys_from_forms/1,
    desugar_recv_funs/1
]).

-include("log.hrl").
-include("typing.hrl").

-spec new_ctx(symtab:t(), symtab:t(), t:opt(ast_check:ty_map())) -> ctx().
new_ctx(Tab, Overlay, Sanity) ->
    new_ctx(Tab, Overlay, Sanity, early_exit, 5000, enabled, dynamic).

-spec new_ctx(symtab:t(), symtab:t(), t:opt(ast_check:ty_map()), feature_flags:report_mode(), pos_integer(), feature_flags:exhaustiveness_mode(), feature_flags:gradual_typing_mode()) -> ctx().
new_ctx(Tab, Overlay, Sanity, ReportMode, ReportTimeout, ExhaustivenessMode, GradualTypingMode) ->
    Ctx = #ctx{ symtab = Tab, overlay_symtab = Overlay, sanity = Sanity, gradual_typing_mode = GradualTypingMode, report_mode = ReportMode, report_timeout = ReportTimeout, exhaustiveness_mode = ExhaustivenessMode },
    Ctx.

% Resolves the set of functions for which a feature is disabled from forms.
% Parses -etylizer({Feature, off}) for module-level and
% -etylizer({Feature, off, [fun/arity]}) for function-level.
-spec resolve_disabled_funs(atom(), ast:forms()) -> sets:set({atom(), arity()}).
resolve_disabled_funs(Feature, Forms) ->
    {ModuleOff, PerFunOff} = lists:foldl(
      fun(Form, {MO, PF}) ->
          case Form of
              {attribute, _, etylizer, {F, off}} when F =:= Feature ->
                  {true, PF};
              {attribute, _, etylizer, {F, off, Funs}} when F =:= Feature ->
                  {MO, sets:union(PF, sets:from_list(Funs))};
              _ -> {MO, PF}
          end
      end,
      {false, sets:new()},
      Forms),
    case ModuleOff of
        true ->
            % Module-level off: all functions are disabled
            lists:foldl(
                fun(Form, Acc) ->
                    case Form of
                        {function, _, Name, Arity, _} -> sets:add_element({Name, Arity}, Acc);
                        _ -> Acc
                    end
                end, sets:new(), Forms);
        false ->
            PerFunOff
    end.

% Extracts per-function receive message types from -etylizer({msg_type, ...}) attributes.
% Format: -etylizer({msg_type, FunName, Arity, ParsedType[, noexhaustiveness]}).
% Must appear before function definitions (OTP 28+ requirement).
% Returns a map from {FunName, Arity} to {declared message type, exhaust | noexhaust}.
-spec recv_msg_tys_from_forms(ast:forms()) -> #{{atom(), arity()} => {ast:ty(), exhaust | noexhaust}}.
recv_msg_tys_from_forms(Forms) ->
    lists:foldl(
      fun(Form, Acc) ->
          case Form of
              {attribute, _, etylizer, {msg_type, FunName, Arity, Ty, noexhaustiveness}} ->
                  maps:put({FunName, Arity}, {Ty, noexhaust}, Acc);
              {attribute, _, etylizer, {msg_type, FunName, Arity, Ty}} ->
                  maps:put({FunName, Arity}, {Ty, exhaust}, Acc);
              _ -> Acc
          end
      end,
      #{},
      Forms).

% Generate the helper function name for a desugared receive.
% If the original function name ends in "_fail" (test-failure naming convention),
% the helper name also ends in "_fail" so the test runner uses check_fail_fun.
-spec mk_recv_help_name(atom(), non_neg_integer()) -> atom().
mk_recv_help_name(FunName, Index) ->
    BaseName = atom_to_list(FunName),
    Suffix = "__" ++ integer_to_list(Index),
    case utils:string_ends_with(BaseName, "_fail") of
        true ->
            Stripped = string:slice(BaseName, 0, string:length(BaseName) - 5),
            list_to_atom("__recv__" ++ Stripped ++ Suffix ++ "_fail");
        false ->
            list_to_atom("__recv__" ++ BaseName ++ Suffix)
    end.

% Desugar list-form msg_type attributes into helper functions with intersection specs.
% For each -etylizer({msg_type, F, N, [FunTy, ...]}) attribute (where FunTy is already
% a parsed ast:ty_full_fun()), creates a helper '__recv__F__0' with case body and
% intersection spec. Removes the list msg_type attribute from the resulting forms.
%
% Strategy A (msg_type arity = function arity): receive in original body is replaced
% by a direct call to the helper passing the original parameters.
%
% Strategy B (msg_type arity > function arity): receive in original body is replaced
% by an untyped pass-through receive that calls the helper with the message.
-spec desugar_recv_funs(ast:forms()) -> ast:forms().
desugar_recv_funs(Forms) ->
    ListMsgTys =
        lists:foldl(
            fun(Form, Acc) ->
                case Form of
                    {attribute, _, etylizer, {msg_type, FunName, Arity, FunTys, noexhaustiveness}}
                            when is_list(FunTys) ->
                        maps:put({FunName, Arity}, {FunTys, noexhaust}, Acc);
                    {attribute, _, etylizer, {msg_type, FunName, Arity, FunTys}}
                            when is_list(FunTys) ->
                        maps:put({FunName, Arity}, {FunTys, exhaust}, Acc);
                    _ -> Acc
                end
            end,
            #{},
            Forms),
    case maps:size(ListMsgTys) of
        0 -> Forms;
        _ ->
            {RevForms, _Done} = lists:foldl(
                fun(Form, {Acc, Done}) ->
                    case Form of
                        {attribute, _, etylizer, {msg_type, _, _, FunTys, noexhaustiveness}}
                                when is_list(FunTys) ->
                            % Drop: replaced by helper function + spec below
                            {Acc, Done};
                        {attribute, _, etylizer, {msg_type, _, _, FunTys}}
                                when is_list(FunTys) ->
                            % Drop: replaced by helper function + spec below
                            {Acc, Done};
                        {function, _, FunName, FunArity, _} ->
                            Key = {FunName, FunArity},
                            case maps:get(Key, ListMsgTys, not_found) of
                                not_found ->
                                    {[Form | Acc], Done};
                                {FunTys, ExhaustFlag} ->
                                    case sets:is_element(Key, Done) of
                                        true ->
                                            {[Form | Acc], Done};
                                        false ->
                                            NewForms = desugar_one(Form, FunTys, ExhaustFlag),
                                            % Prepend in reverse (reversed list, so last-inserted
                                            % = first in final output). NewForms is [Fun, Spec, Helper]
                                            % (or [MsgTyAttr, Fun, Spec, Helper] for Strategy B).
                                            {lists:reverse(NewForms) ++ Acc,
                                             sets:add_element(Key, Done)}
                                    end
                            end;
                        _ ->
                            {[Form | Acc], Done}
                    end
                end,
                {[], sets:new()},
                Forms),
            lists:reverse(RevForms)
    end.

% Desugar a single function with list msg_type.
% Returns the list of forms to insert in place of the function + msg_type attribute.
% For Strategy A: [NewFun, HelpSpec, HelpFun]
% For Strategy B: [MsgTypeAttr, NewFun, HelpSpec, HelpFun]
%   MsgTypeAttr pins the outer receive's message type to term() so that the original
%   function's return type can be properly checked against its spec.
% ExhaustFlag is exhaust | noexhaust, propagated to the helper's msg_type attribute.
-spec desugar_one(ast:fun_decl(), [ast:ty_full_fun()], exhaust | noexhaust) -> [ast:form()].
desugar_one({function, Loc, FunName, FunArity, Clauses}, FunTys, ExhaustFlag) ->
    [{fun_full, ArgTys, _} | _] = FunTys,
    HelpArity = length(ArgTys),
    HelpName = mk_recv_help_name(FunName, 0),
    if
        HelpArity =:= FunArity ->
            {NewFun, HelpSpec, HelpFun} =
                desugar_strategy_a(Loc, FunName, FunArity, Clauses, FunTys, HelpName, HelpArity),
            [NewFun, HelpSpec, HelpFun];
        HelpArity > FunArity ->
            {NewFun, HelpSpec, HelpFun} =
                desugar_strategy_b(Loc, FunName, FunArity, Clauses, FunTys, HelpName, HelpArity),
            % Add a bare msg_type for the outer pass-through receive (term() = top type).
            % This pins _Msg to term() so helper(term()) is used, enabling meaningful
            % return-type checking against the original function's spec.
            % Inherit exhaustiveness flag from the original msg_type.
            MsgTypeAttr = case ExhaustFlag of
                exhaust ->
                    {attribute, Loc, etylizer,
                     {msg_type, FunName, FunArity, {predef_alias, term}}};
                noexhaust ->
                    {attribute, Loc, etylizer,
                     {msg_type, FunName, FunArity, {predef_alias, term}, noexhaustiveness}}
            end,
            [MsgTypeAttr, NewFun, HelpSpec, HelpFun];
        true ->
            errors:ty_error(Loc,
                "msg_type list arity ~w < function arity ~w for ~w/~w",
                [HelpArity, FunArity, FunName, FunArity])
    end.

% Strategy A: msg_type arity = function arity.
% Replaces the receive in the function body with a direct call to the helper.
% The original function parameters become the helper's arguments.
-spec desugar_strategy_a(ast:loc(), atom(), arity(), [ast:fun_clause()],
    [ast:ty_full_fun()], atom(), arity()) ->
    {ast:fun_decl(), ast:fun_spec(), ast:fun_decl()}.
desugar_strategy_a(Loc, FunName, FunArity, Clauses, FunTys, HelpName, HelpArity) ->
    [{fun_clause, CLoc, Pats, Guards, Body} | RestClauses] = Clauses,
    case extract_recv_from_body(Body) of
        {RecvCases, RecvKind, PreBody} ->
            T1 = erlang:unique_integer([positive]),
            T2 = erlang:unique_integer([positive]),
            % Helper: fresh params, body = case on first param
            HelpParams = mk_fresh_binds(Loc, HelpArity, T1),
            {var, HP0Loc, {local_bind, HP0Name}} = hd(HelpParams),
            HP0Ref = {var, HP0Loc, {local_ref, HP0Name}},
            HelpBody = [mk_case_from_recv(RecvKind, Loc, HP0Ref, RecvCases)],
            HelpFun = {function, Loc, HelpName, HelpArity,
                       [{fun_clause, Loc, HelpParams, [], HelpBody}]},
            HelpSpec = mk_help_spec(Loc, HelpName, HelpArity, FunTys),
            % Original: convert pats to vars, replace receive with call to helper
            {NewPats, ArgRefs} = collect_param_refs(Loc, Pats, T2),
            CallExpr = {call, Loc,
                        {var, Loc, {ref, HelpName, HelpArity}},
                        ArgRefs},
            NewFun = {function, Loc, FunName, FunArity,
                      [{fun_clause, CLoc, NewPats, Guards, PreBody ++ [CallExpr]}
                       | RestClauses]},
            {NewFun, HelpSpec, HelpFun};
        error ->
            errors:ty_error(Loc,
                "msg_type list: no receive found in body of ~w/~w",
                [FunName, FunArity])
    end.

% Strategy B: msg_type arity > function arity (e.g., 0-arg function, 1-arg msg_type).
% The original function gets an untyped pass-through receive; the helper holds the
% receive patterns as a case expression.
-spec desugar_strategy_b(ast:loc(), atom(), arity(), [ast:fun_clause()],
    [ast:ty_full_fun()], atom(), arity()) ->
    {ast:fun_decl(), ast:fun_spec(), ast:fun_decl()}.
desugar_strategy_b(Loc, FunName, FunArity, Clauses, FunTys, HelpName, HelpArity) ->
    [{fun_clause, CLoc, Pats, Guards, Body} | RestClauses] = Clauses,
    case extract_recv_from_body(Body) of
        {RecvCases, RecvKind, PreBody} ->
            T1 = erlang:unique_integer([positive]),
            T2 = erlang:unique_integer([positive]),
            % Helper: first param is the message, body = case on it
            HelpParams = mk_fresh_binds(Loc, HelpArity, T1),
            {var, HMsgLoc, {local_bind, HMsgName}} = hd(HelpParams),
            HMsgRef = {var, HMsgLoc, {local_ref, HMsgName}},
            HelpBody = [mk_case_from_recv(RecvKind, Loc, HMsgRef, RecvCases)],
            HelpFun = {function, Loc, HelpName, HelpArity,
                       [{fun_clause, Loc, HelpParams, [], HelpBody}]},
            HelpSpec = mk_help_spec(Loc, HelpName, HelpArity, FunTys),
            % Original: replace receive with untyped pass-through
            MsgBind = {var, Loc, {local_bind, {'__RecvMsg', T2}}},
            MsgRef  = {var, Loc, {local_ref,  {'__RecvMsg', T2}}},
            CallExpr = {call, Loc,
                        {var, Loc, {ref, HelpName, HelpArity}},
                        [MsgRef]},
            PassThruClause = {case_clause, Loc, MsgBind, [], [CallExpr]},
            OuterRecv = case RecvKind of
                simple ->
                    {'receive', Loc, [PassThruClause]};
                {after_expr, AfterBody, TimerExp} ->
                    {receive_after, Loc, [PassThruClause], TimerExp, AfterBody}
            end,
            NewFun = {function, Loc, FunName, FunArity,
                      [{fun_clause, CLoc, Pats, Guards, PreBody ++ [OuterRecv]}
                       | RestClauses]},
            {NewFun, HelpSpec, HelpFun};
        error ->
            errors:ty_error(Loc,
                "msg_type list: no receive found in body of ~w/~w",
                [FunName, FunArity])
    end.

% Find the receive or receive_after at the end of a body expression list.
-spec extract_recv_from_body([ast:exp()]) ->
    error | {[ast:case_clause()],
             simple | {after_expr, [ast:exp()], ast:exp()},
             [ast:exp()]}.
extract_recv_from_body([]) -> error;
extract_recv_from_body(Body) ->
    case lists:last(Body) of
        {'receive', _Loc, Cases} ->
            {Cases, simple, lists:droplast(Body)};
        % With an escape annotation (added by the case-binding propagation pass).
        % The annotation is dropped: the receive becomes a case whose clause patterns
        % carry the bindings, so it is recomputed during case typing.
        {'receive', _Loc, Cases, _Escape} ->
            {Cases, simple, lists:droplast(Body)};
        {receive_after, _Loc, Cases, TimerExp, AfterBody} ->
            {Cases, {after_expr, AfterBody, TimerExp}, lists:droplast(Body)};
        {receive_after, _Loc, Cases, TimerExp, AfterBody, _Escape} ->
            {Cases, {after_expr, AfterBody, TimerExp}, lists:droplast(Body)};
        _ ->
            error
    end.

% Build a case expression from receive cases.
% For Strategy A with after: the after clause is dropped (timer semantics not needed
% for type checking the patterns).
-spec mk_case_from_recv(simple | {after_expr, [ast:exp()], ast:exp()},
    ast:loc(), ast:exp(), [ast:case_clause()]) -> ast:exp_case().
mk_case_from_recv(simple, Loc, Scrutinee, Cases) ->
    {'case', Loc, Scrutinee, Cases};
mk_case_from_recv({after_expr, _AfterBody, _TimerExp}, Loc, Scrutinee, Cases) ->
    {'case', Loc, Scrutinee, Cases}.

% Build a list of N fresh parameter bindings starting at BaseToken.
-spec mk_fresh_binds(ast:loc(), arity(), integer()) -> [ast:pat_var()].
mk_fresh_binds(Loc, N, BaseToken) ->
    [{var, Loc, {local_bind, {'__RecvP', BaseToken + I}}} || I <- lists:seq(0, N - 1)].

% Build the helper function spec form.
-spec mk_help_spec(ast:loc(), atom(), arity(), [ast:ty_full_fun()]) -> ast:fun_spec().
mk_help_spec(Loc, HelpName, HelpArity, FunTys) ->
    Ty = case FunTys of
        [Single] -> Single;
        _        -> {intersection, FunTys}
    end,
    {attribute, Loc, spec, HelpName, HelpArity, {ty_scheme, [], Ty}, without_mod}.

% Convert function parameter patterns to fresh variable bindings + references.
% Wildcards become fresh vars; existing var-binds are reused; complex patterns
% get a compound match (VarBind = OrigPat) added.
-spec collect_param_refs(ast:loc(), [ast:pat()], integer()) ->
    {[ast:pat()], [ast:exp_var()]}.
collect_param_refs(_Loc, Pats, BaseToken) ->
    lists:unzip(
        lists:zipwith(
            fun(Pat, I) ->
                Tok = BaseToken + I,
                case Pat of
                    {wildcard, PLoc} ->
                        VName = {'__RecvP', Tok},
                        {{var, PLoc, {local_bind, VName}},
                         {var, PLoc, {local_ref,  VName}}};
                    {var, PLoc, {local_bind, VName}} ->
                        {Pat, {var, PLoc, {local_ref, VName}}};
                    _ ->
                        PLoc = element(2, Pat),
                        VName = {'__RecvP', Tok},
                        {{match, PLoc, {var, PLoc, {local_bind, VName}}, Pat},
                         {var, PLoc, {local_ref, VName}}}
                end
            end,
            Pats,
            lists:seq(0, length(Pats) - 1))).

% Checks all forms of a module
-spec check_forms(ctx(), string(), ast:forms(), sets:set(string()), sets:set(string()), boolean()) -> [{atom(), arity()}].
check_forms(Ctx, FileName, Forms, Only, Ignore, CheckExports) ->
    check_forms(Ctx, FileName, Forms, Only, Ignore, CheckExports, {sets:new(), sets:new()}).

-spec check_forms(ctx(), string(), ast:forms(), sets:set(string()), sets:set(string()), boolean(), {sets:set({atom(), arity()}), sets:set({atom(), arity()})}) -> [{atom(), arity()}].
check_forms(Ctx, FileName, Forms, Only, Ignore, CheckExports, {CliNoExhaustiveness, CliNoRedundancy}) ->
    case CheckExports orelse Ctx#ctx.gradual_typing_mode =:= infer of
        true ->
            ?LOG_DEBUG("Checking whether exported functions in ~s have a type spec", FileName),
            check_exported_funs_specified(Forms);
        false ->
            ?LOG_DEBUG("Skipping check for exported functions in ~s", FileName)
    end,
    % Desugar list-form msg_type attributes into helper functions with intersection specs.
    DesugaredForms = desugar_recv_funs(Forms),
    ExtTab = symtab:extend_symtab(FileName, DesugaredForms, Ctx#ctx.symtab, Ctx#ctx.overlay_symtab),
    DisableExhaustiveness = sets:union(resolve_disabled_funs(functions_exhaustive, DesugaredForms), CliNoExhaustiveness),
    DisableRedundancy = sets:union(resolve_disabled_funs(functions_redundant, DesugaredForms), CliNoRedundancy),
    RecvMsgTys = recv_msg_tys_from_forms(DesugaredForms),
    ExtCtx = Ctx#ctx { symtab = ExtTab, disable_exhaustiveness = DisableExhaustiveness, disable_redundancy = DisableRedundancy, recv_msg_tys = RecvMsgTys },
    ?LOG_DEBUG("Only: ~200p", sets:to_list(Only)),
    ?LOG_DEBUG("Ignore: ~200p", sets:to_list(Ignore)),
    % Split in functions with and without tyspec
    GradualMode = ExtCtx#ctx.gradual_typing_mode,
    {FunsWithSpec, FunsWithoutSpec, KnownFuns} =
        lists:foldr(
          fun(Form, Acc = {With, Without, Knowns}) ->
            case Form of
                {function, Loc, Name, Arity, _Clauses} ->
                    ModuleName = ast_utils:modname_from_path(FileName),
                    Ref = {ref, Name, Arity},
                    RefStr = utils:sformat("~w/~w", Name, Arity),
                    QRefStr = utils:sformat("~w:~s", ModuleName, RefStr),
                    NameStr = utils:sformat("~w", Name),
                    ModStr = utils:sformat("~w", ModuleName),
                    X = {QRefStr, RefStr, NameStr, ModStr},
                    Check = should_check(QRefStr, RefStr, NameStr, ModStr, Only, Ignore),
                    case symtab:find_fun(Ref, ExtTab) of
                        error ->
                            if
                              Check ->
                                  case GradualMode of
                                      dynamic ->
                                          DynTy = dynamic_ty_scheme(Arity),
                                          {[{Form, DynTy} | With], Without, [X | Knowns]};
                                      infer ->
                                          {With, [Form | Without], [X | Knowns]}
                                  end;
                              true ->
                                  case GradualMode of
                                      dynamic ->
                                          {With, Without, [X | Knowns]};
                                      infer ->
                                          errors:some_error(
                                              "~s: Cannot ignore function without type spec: ~s", [FileName, RefStr]
                                          )
                                  end
                            end;
                        {ok, Ty} ->
                            if
                                Check -> {[{Form, Ty} | With], Without, [X | Knowns]};
                                true ->
                                    ?LOG_TRACE("~s: not type checking function ~s as requested",
                                               ast:format_loc(Loc), RefStr),
                                    {With, Without, [X | Knowns]}
                            end
                    end;
                _ -> Acc
            end
          end,
          {[], [], []},
          DesugaredForms
         ),
    % Make sure that Only does not contain an unknown function
    AllKnown = lists:flatmap(fun({QRef, Ref, N, M}) -> [QRef, Ref, N, M] end, KnownFuns),
    Unknowns = sets:subtract(Only, sets:from_list(AllKnown, [{version, 2}])),
    case sets:is_empty(Unknowns) of
        true -> ok;
        false ->
            ?LOG_INFO("Unknown functions in only: ~200p", sets:to_list(Unknowns))
    end,
    % Infer types of functions without spec (empty in dynamic mode)
    InferredTyEnvs = typing_infer:infer_all(ExtCtx, FileName, FunsWithoutSpec),
    % Typechecks the functions with a type spec. We need to check against all InferredTyEnvs,
    % we can stop on the first success.
    ?LOG_DEBUG("Checking ~w functions in ~s against their specs (~w environments)",
              length(FunsWithSpec), FileName, length(InferredTyEnvs)),

    % if in report mode, continue type checking
    ReportMode = Ctx#ctx.report_mode,
    Loop =
        fun Loop(Envs, Errs) ->
                case Envs of
                    [] ->
                        case Errs of
                            [] -> errors:bug("Lists of errors empty");
                            [{_, Msg}] -> errors:ty_error(Msg);
                            _ ->
                                Formatted =
                                    utils:map_flip(
                                      Errs,
                                      fun({Env, Msg}) ->
                                              utils:sformat("~s:\nEnv: ~s",
                                                            Msg,
                                                            pretty:render_fun_env(Env))
                                      end
                                     ),
                                Msg = utils:sformat("Checking functions against their specs " ++
                                                        "failed for all ~w type environments " ++
                                                        "inferred from functions without " ++
                                                        "specs.\n\n~s",
                                                    length(Errs), string:join(Formatted, "\n\n")),
                                errors:ty_error(Msg)
                        end;
                    [E | RestEnvs] ->
                        case ReportMode of
                            early_exit ->
                                case typing_check:check_all(ExtCtx, FileName, E, FunsWithSpec) of
                                    ok -> []; % we are done
                                    {error, Msg} -> Loop(RestEnvs, [{E, Msg} | Errs])
                                end;
                            report ->
                                typing_check:check_all_report(ExtCtx, FileName, E, FunsWithSpec)
                        end
                end
        end,
    FailedFuns = Loop(InferredTyEnvs, []),
    ?LOG_INFO("Checking ~w functions in ~s against their specs finished successfully",
              length(FunsWithSpec), FileName),
    FailedFuns.

-spec should_check(string(), string(), string(), string(), sets:set(string()), sets:set(string())) -> boolean().
should_check(QRefStr, RefStr, NameStr, ModStr, Only, Ignore) ->
    case sets:is_empty(Only) of
        true ->
            not (sets:is_element(QRefStr, Ignore)
                    orelse sets:is_element(RefStr, Ignore)
                    orelse sets:is_element(NameStr, Ignore)
                    orelse sets:is_element(ModStr, Ignore));
        false ->
            sets:is_element(QRefStr, Only)
                orelse sets:is_element(RefStr, Only)
                orelse sets:is_element(NameStr, Only)
                orelse sets:is_element(ModStr, Only)
    end.

% Creates a dynamic type scheme for a function with the given arity.
-spec dynamic_ty_scheme(non_neg_integer()) -> ast:ty_scheme().
dynamic_ty_scheme(Arity) ->
    DynamicArgs = lists:duplicate(Arity, {predef, dynamic}),
    {ty_scheme, [], {fun_full, DynamicArgs, {predef, dynamic}}}.

-spec check_exported_funs_specified(ast:forms()) -> ok | no_return().
check_exported_funs_specified(Forms) ->
    Exported = [Exp || {attribute, _, export, Exports} <- Forms, Exp <- Exports],
    Speced = [{Fun, Arity} || {attribute, _, spec, Fun, Arity, _, _} <- Forms],
    Missing = [ utils:sformat("~w/~w", Fun, Arity) || {Fun, Arity} <- Exported, not lists:member({Fun, Arity}, Speced) ],
    case Missing of
        [] -> ok;
    _ ->
        errors:ty_error(utils:sformat("The following exported functions have no type specification: ~s", [string:join(Missing, ", ")]))
    end.
