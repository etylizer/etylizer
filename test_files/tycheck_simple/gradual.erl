-module(gradual).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

% Some tests modified from Gradualizer and eqWAlizer

-spec down(dynamic()) -> integer().
down(X) -> X.

-spec up(integer()) -> dynamic().
up(X) -> X.

-spec fun_down(fun((integer()) -> dynamic())) -> fun((integer()) -> atom()).
fun_down(X) -> X.

-spec fun_down_fail(fun((integer()) -> dynamic())) -> fun((string()) -> atom()).
fun_down_fail(X) -> X.

-spec fun_down2(fun((dynamic()) -> atom())) -> fun((integer()) -> atom()).
fun_down2(X) -> X.

-spec fun_up(fun((integer()) -> atom())) -> fun((integer()) -> dynamic()).
fun_up(X) -> X.

-spec fun_up_fail(fun((integer()) -> atom())) -> fun((string()) -> dynamic()).
fun_up_fail(X) -> X.

-spec fun_up2(fun((integer()) -> atom())) -> fun((dynamic()) -> atom()).
fun_up2(X) -> X.

-spec fun_mixed(fun((integer(), string(), dynamic()) -> {atom(), dynamic()})) ->
    fun((integer(), dynamic(), float()) -> {dynamic(), integer()}).
fun_mixed(X) -> X.

%% NOTE (Lanvin Ch. 6 / empty domains): this passes in etylizer because
%% the tally assigns the frame variable for dynamic() in arg2 of the RHS to
%% none(), making the RHS argument tuple {atom(), none(), float()} = none().
%% A function is trivially a subtype of none()->T for any T.
%% Under Lanvin's modified semantic subtyping (Def. 6.5, p. 111), where
%% 0→τ and 0→τ' are NOT considered equivalent, this would be rejected.
%% The root cause is modeling multi-arg functions as tuples: a single
%% frame-variable component can collapse the whole tuple to none().
-spec fun_mixed2(fun((integer(), string(), dynamic()) -> {atom(), dynamic()})) ->
    fun((atom(), dynamic(), float()) -> {dynamic(), integer()}).
fun_mixed2(X) -> X.

-spec fun_mixed3(fun((integer(), string(), dynamic()) -> {atom(), dynamic()})) ->
    fun((integer(), dynamic(), float()) -> {float(), integer()}).
fun_mixed3(X) -> X.

-spec list_down(list(dynamic())) -> list(integer()).
list_down(X) -> X.

-spec list_up(list(integer())) -> list(dynamic()).
list_up(X) -> X.

-spec tuple_down({integer(), dynamic(), atom()}) -> {integer(), string(), atom()}.
tuple_down(X) -> X.

-spec tuple_down2({integer(), dynamic(), atom()}) -> {integer(), string(), float()}.
tuple_down2(X) -> X.

-spec tuple_up({integer(), string(), atom()}) -> {integer(), dynamic(), atom()}.
tuple_up(X) -> X.

-spec tuple_up_fail({integer(), string(), atom()}) -> {integer(), dynamic(), float()}.
tuple_up_fail(X) -> X.

-spec tuple_up_down({dynamic(), string(), atom()}) -> {integer(), dynamic(), atom()}.
tuple_up_down(X) -> X.

-spec tuple_up_down2({dynamic(), string(), atom()}) -> {integer(), dynamic(), float()}.
tuple_up_down2(X) -> X.

-spec refine_times_01(dynamic()) -> integer().
refine_times_01(X) ->
    case X of
        Y when is_integer(Y) -> Y;
        _ -> error(badarg)
    end.

-spec refine_times_02_fail(dynamic()) -> integer().
refine_times_02_fail(X) ->
    case X of
        Y when is_atom(Y) ->
            case Y of
                Z when is_integer(Z) -> Z;
                _ -> error(badarg)
            end;
        _ -> error(badarg)
    end.

-spec refine_times_03_fail(dynamic()) -> integer().
refine_times_03_fail(X) ->
    case X of
        Y when is_atom(Y) ->
            case Y of
                Z when is_atom(Z) -> 
                    case Z of
                        B when is_integer(B) -> B;
                        _ -> error(badarg)
                    end;
                _ -> error(badarg)
            end;
        _ -> error(badarg)
    end.

% second branch is still valid, dynamic()
-spec refine_guard_atom(dynamic()) -> atom().
refine_guard_atom(Dyn) ->
  case Dyn of
    A when is_atom(A) -> A;
    B -> B
  end.

% dynamic() tuple extraction
-spec refine_pattern_atom(dynamic()) -> integer().
refine_pattern_atom(Dyn) ->
  case Dyn of
    a -> 0;
    {_, I} -> I
  end.

-spec refine_pattern_tuple(dynamic()) -> atom().
refine_pattern_tuple(Dyn) ->
  case Dyn of
    {a, A} -> A;
    {_, B} -> B
  end.

-spec refine_union_01(dynamic() | error) -> ok.
refine_union_01(error) -> ok;
refine_union_01(D) -> D.

-spec refine_union_02(dynamic() | error | ok) -> ok.
refine_union_02(error) -> ok;
refine_union_02(D) -> D.

% fail: error branch missing
-spec refine_union_03_fail(dynamic() | error | ok) -> ok.
refine_union_03_fail(ok) -> ok;
refine_union_03_fail(D) -> D.

% exhaustiveness is not checked with dynamic
-spec refine_exhaustive_01(dynamic()) -> ok.
refine_exhaustive_01(X) when is_integer(X) -> X.

% but with concrete types
-spec refine_exhaustive_02_fail(dynamic() | error) -> integer().
refine_exhaustive_02_fail(U) when is_integer(U) -> U.

% refine inside tuples
-spec refine_exhaustive_03({dynamic() | err}) -> ok.
refine_exhaustive_03({err}) -> ok;
refine_exhaustive_03({X}) -> X.

-type union() :: {dynamic() | err}.
-spec refine_exhaustive_04(union()) -> ok.
refine_exhaustive_04({err}) -> ok;
refine_exhaustive_04({X}) -> X.

% Refine dynamic in tuple union
-type dyn_alias() :: dynamic().
-type dyn_nested() :: {integer(), dyn_alias()}.
-type spec_union() :: {dyn_alias() | err}.

-spec refine_union_alias(union()) -> ok.
refine_union_alias({err}) -> ok;
refine_union_alias({X}) -> X.

-spec refine_union_alias_fail(union()) -> ok.
refine_union_alias_fail({X}) -> X.

-spec refine_to_tuple(union()) -> {ok}.
refine_to_tuple({err}) -> {ok};
refine_to_tuple(X) -> X.

-spec refine_in_tuple(union()) -> spec_union().
refine_in_tuple(T) -> T.

-spec refine_in_tuple_fail(union()) -> {ok}.
refine_in_tuple_fail(T) -> T.

% Refine dynamic in tuple with multiple tagged variants
-spec refine_tagged_tuple({err, binary()} | {ok, atom()} | dynamic()) -> binary().
refine_tagged_tuple({err, B}) -> B;
refine_tagged_tuple({ok, A}) -> atom_to_binary(A);
refine_tagged_tuple(V) -> V.

-type dyn_or_none() :: dynamic() | none.

-spec dyn_union_simple1(term()) -> dyn_or_none().
dyn_union_simple1(_) -> error(test).

-spec dyn_union_case_01(term()) -> atom().
dyn_union_case_01(X) ->
  Maybe = dyn_union_simple1(X),
  case Maybe of
    none -> ok;
    Atom -> Atom
  end.

-spec dyn_union_case_02(term(), term()) -> {atom(), atom()}.
dyn_union_case_02(X, Y) ->
  Maybe1 = dyn_union_simple1(X),
  Maybe2 = dyn_union_simple1(Y),
  case {Maybe1, Maybe2} of
    {none, none} ->
      {ok, ok};
    {Atom1, none} ->
      {Atom1, ok};
    {none, Atom2} ->
      {ok, Atom2};
    {Atom1, Atom2} ->
      {Atom1, Atom2}
  end.

-spec use_dynamic_type(dynamic()) -> {atom()}.
use_dynamic_type(Dyn) -> {Dyn}.

-spec use_dynamic_type_fail(dynamic()) -> {atom()}.
use_dynamic_type_fail(Dyn) ->
  {erlang:atom_to_binary(Dyn)}.

-spec dyn_val() -> dynamic().
dyn_val() -> error(dynamic).

-spec andalso_dyn_01() -> false.
andalso_dyn_01() ->
  dyn_val() andalso false.

-spec andalso_dyn_02() -> true.
andalso_dyn_02() ->
  true andalso dyn_val().

%% ============================================================
%% Tests from Petrucciani thesis (Part II, Chapters 9-10)
%% ============================================================

%% A dynamic() argument can be used in two different type contexts
%% simultaneously (arithmetic AND predicate), because each use
%% independently materializes the ? to whatever concrete type is needed.
-spec dyn_two_uses_01(dynamic()) -> {number(), boolean()}.
dyn_two_uses_01(X) -> {X + 1, is_atom(X)}.

-spec dyn_two_uses_02(dynamic()) -> {integer(), boolean()}.
dyn_two_uses_02(X) -> {erlang:round(X), X =:= 0}.

%% Applying a dynamic value as a function.
%% dynamic() can be applied as if it were fun((integer()) -> dynamic()),
%% since ? materializes to any function type.
-spec dyn_fun_app_01(dynamic(), integer()) -> dynamic().
dyn_fun_app_01(F, X) -> F(X).

%% Even a fully-dynamic function applied to a dynamic arg.
-spec dyn_fun_app_02(dynamic(), dynamic()) -> dynamic().
dyn_fun_app_02(F, X) -> F(X).

%% Proposition 9.10 (relation to Garcia-Cimini ITGL):
-spec poly_dyn_01(fun((A) -> A), dynamic()) -> dynamic().
poly_dyn_01(F, X) -> F(X).

-spec mater_trans_01(fun((dynamic()) -> dynamic())) -> fun((integer()) -> atom()).
mater_trans_01(F) -> F.

%% Extended transitivity: ? -> ? -> ? materializes to integer() -> atom() -> boolean().
-spec mater_trans_02(fun((dynamic()) -> fun((dynamic()) -> dynamic()))) ->
    fun((integer()) -> fun((atom()) -> boolean())).
mater_trans_02(F) -> F.

% Dynamic call with 0 args
-spec dyn_call_01(atom(), atom()) -> integer().
dyn_call_01(M, F) ->
  M:F().

% Dynamic call with 1 arg
-spec dyn_call_02(atom(), atom(), integer()) -> integer().
dyn_call_02(M, F, Arg) ->
  M:F(Arg).

% Dynamic call with 2 args
-spec dyn_call_03(atom(), atom(), integer(), atom()) -> integer().
dyn_call_03(M, F, Arg1, Arg2) ->
  M:F(Arg1, Arg2).

% Dynamic call result bound to variable, 0 args
-spec dyn_call_eval_01(atom(), atom()) -> integer().
dyn_call_eval_01(M, F) ->
  Res = M:F(),
  Res.

% Dynamic call result bound to variable, 1 arg
-spec dyn_call_eval_02(atom(), atom(), integer()) -> integer().
dyn_call_eval_02(M, F, Arg) ->
  Res = M:F(Arg),
  Res.

% Dynamic call result bound to variable, 2 args
-spec dyn_call_eval_03(atom(), atom(), integer(), atom()) -> integer().
dyn_call_eval_03(M, F, Arg1, Arg2) ->
  Res = M:F(Arg1, Arg2),
  Res.

% dynamic hidden behind a named type alias — the case branch with atom()
% must NOT be reported as redundant because dyn_alias() = dynamic().
-spec named_dyn_case_01(dyn_alias()) -> integer().
named_dyn_case_01(X) ->
    case X of
        Y when is_integer(Y) -> Y;
        _ -> 0
    end.

% dynamic hidden one level deeper — dyn_nested() = {integer(), dyn_alias()}
-spec named_dyn_case_02(dyn_nested()) -> integer().
named_dyn_case_02(X) ->
    case X of
        {N, _} when is_integer(N) -> N;
        _ -> 0
    end.
