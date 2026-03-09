-module(nominal).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

-nominal meter() :: integer().
-nominal foot() :: integer().

-type regular_int() :: integer().
-type regular_nominal_meter() :: meter().

%%%%%%%%%%%%%%%%%%%%%%%% BASIC IDENTITY %%%%%%%%%%%%%%%%%%%%%%%

% Same nominal type: should pass
-spec same_nominal_01(meter()) -> meter().
same_nominal_01(X) -> X.

-spec same_nominal_02(meter()) -> regular_nominal_meter().
same_nominal_02(X) -> X.

-spec same_nominal_03(regular_nominal_meter()) -> meter().
same_nominal_03(X) -> X.

-spec same_nominal_04(regular_nominal_meter()) -> regular_nominal_meter().
same_nominal_04(X) -> X.

%%%%%%%%%%%%%%%%%%%%%%%% INCOMPATIBLE NOMINALS %%%%%%%%%%%%%%%%%%%%%%%

% Different nominal types: should fail
-spec different_nominal_01_fail(meter()) -> foot().
different_nominal_01_fail(X) -> X.

-spec different_nominal_02_fail(foot()) -> meter().
different_nominal_02_fail(X) -> X.

%%%%%%%%%%%%%%%%%%%%%%%% STRUCTURAL COMPATIBILITY %%%%%%%%%%%%%%%%%%%%%%%

% Nominal to structural
-spec nominal_to_structural_01(meter()) -> integer().
nominal_to_structural_01(X) -> X.

% Structural to nominal
-spec structural_to_nominal_01(integer()) -> meter().
structural_to_nominal_01(X) -> X.

% Nominal to regular type alias: should pass
-spec nominal_to_alias_01(meter()) -> regular_int().
nominal_to_alias_01(X) -> X.

% Regular type alias to nominal: should pass
-spec alias_to_nominal_01(regular_int()) -> meter().
alias_to_nominal_01(X) -> X.

-spec unused_nominal_01(meter()) -> foot().
unused_nominal_01(_) -> 42.

-spec dead_branch_01(meter() | atom()) -> integer() | atom().
dead_branch_01(X) -> X.


%%%%%%%%%%%%%%%%%%%%%%%% COMPOUND TYPES %%%%%%%%%%%%%%%%%%%%%%%

-spec tuple_same_01({meter(), foot()}) -> {meter(), foot()}.
tuple_same_01(X) -> X.

-spec tuple_different_01_fail({meter()}) -> {foot()}.
tuple_different_01_fail(X) -> X.

-spec mixed_tuple_01({meter(), integer()}) -> {meter(), integer()}.
mixed_tuple_01(X) -> X.

-spec nominal_any_01(meter()) -> any().
nominal_any_01(X) -> X.

%%%%%%%%%%%%%%%%%%%%%%%% FUNCTION CALLS %%%%%%%%%%%%%%%%%%%%%%%

-spec call_same_01(meter()) -> meter().
call_same_01(X) -> same_nominal_01(X).

-spec nominal_add_01(meter(), meter()) -> integer().
nominal_add_01(X, Y) -> X + Y.

%%%%%%%%%%%%%%%%%%%%%%%% CHAINS THROUGH POLYMORPHIC CALLS %%%%%%%%%%%%%%%%%%%%%%%

% Polymorphic identity helper
-spec nominal_id(A) -> A.
nominal_id(X) -> X.

% Passing meter() through a polymorphic id and returning as foot()
% The nominal incompatibility is hidden behind a variable chain:
%   meter() <: $1, $1 <: $fresh, $fresh <: foot()
-spec chain_01_fail(meter()) -> foot().
chain_01_fail(X) -> nominal_id(X).

% Same nominal through polymorphic id
-spec chain_02(meter()) -> meter().
chain_02(X) -> nominal_id(X).

% Chain through tuple construction with polymorphic call
-spec chain_03_fail(meter()) -> {foot()}.
chain_03_fail(X) -> {nominal_id(X)}.

% Same nominal in tuple through polymorphic call: should pass
-spec chain_04(meter()) -> {meter()}.
chain_04(X) -> {nominal_id(X)}.

% Wrapping/unwrapping helpers to force tuple-boundary variable chains
-spec wrap(A) -> {A}.
wrap(X) -> {X}.

-spec unwrap({A}) -> A.
unwrap({X}) -> X.

% Single tuple boundary chain: should fail (and does — one tuple boundary works)
-spec chain_tuple_01_fail(meter()) -> foot().
chain_tuple_01_fail(X) -> unwrap(wrap(nominal_id(X))).

% Two tuple boundaries with variable chain between them: should fail
% Generates: meter() -> $a, $a <: $b, {$b} <: {$c}, $c <: $d, {$d} <: {$e}, $e <: foot()
% The variable graph misses the $b->$c and $d->$e edges inside tuples,
% breaking the transitive chain.
-spec chain_tuple_02_fail(meter()) -> foot().
chain_tuple_02_fail(X) -> unwrap(wrap(unwrap(wrap(nominal_id(X))))).

% Named type boundary helpers
-spec named_wrap(A) -> wrapper(A).
named_wrap(X) -> {ok, X}.

-spec named_unwrap(wrapper(A)) -> A.
named_unwrap({ok, X}) -> X.

% Two named-type boundaries with variable chain between: should fail
% Similar to chain_tuple_02 but through wrapper() named types.
-spec chain_named_01_fail(meter()) -> foot().
chain_named_01_fail(X) -> named_unwrap(named_wrap(named_unwrap(named_wrap(nominal_id(X))))).

-spec mu_wrap(A) -> etylizer:mu(nil | {A, etylizer:mu_var()}).
mu_wrap(X) -> {X, nil}.

-spec mu_unwrap(etylizer:mu(nil | {A, etylizer:mu_var()})) -> A.
mu_unwrap({X, _}) -> X;
mu_unwrap(nil) -> error(none).

% Mu type boundary: chain through recursive type wrap/unwrap: should fail
-spec chain_mu_01_fail(meter()) -> foot().
chain_mu_01_fail(X) -> mu_unwrap(mu_wrap(mu_unwrap(mu_wrap(nominal_id(X))))).

%%%%%%%%%%%%%%%%%%%%%%%% NOMINAL INSIDE NAMED TYPES %%%%%%%%%%%%%%%%%%%%%%%

-type wrapper(A) :: {ok, A}.

% Same nominal through wrapper: should pass
-spec wrapper_01(wrapper(meter())) -> wrapper(meter()).
wrapper_01(X) -> X.

% Different nominals through wrapper: should fail
-spec wrapper_02_fail(wrapper(meter())) -> wrapper(foot()).
wrapper_02_fail(X) -> X.

% Wrapper with polymorphic chain: should fail
-spec wrapper_03_fail(wrapper(meter())) -> wrapper(foot()).
wrapper_03_fail(X) -> nominal_id(X).

% Deep nesting: wrapper inside wrapper
-type nested(A) :: wrapper(wrapper(A)).

-spec nested_01_fail(nested(meter())) -> nested(foot()).
nested_01_fail(X) -> X.

% Same nested nominal: should pass
-spec nested_02(nested(meter())) -> nested(meter()).
nested_02(X) -> X.

%%%%%%%%%%%%%%%%%%%%%%%% UNIONS WITH NOMINALS %%%%%%%%%%%%%%%%%%%%%%%

% Union of nominals to one: should fail
% foot() in the union is not a subtype of meter()
-spec union_downcast_01_fail(meter() | foot()) -> meter().
union_downcast_01_fail(X) -> X.

% Same nominal union: should pass
-spec union_same_01(meter() | meter()) -> meter().
union_same_01(X) -> X.

% Union with structural: should pass (structural is compatible)
-spec union_structural_01(meter() | integer()) -> meter().
union_structural_01(X) -> X.

% Union downcast through polymorphic call: should fail
-spec union_chain_01_fail(meter() | foot()) -> meter().
union_chain_01_fail(X) -> nominal_id(X).

%%%%%%%%%%%%%%%%%%%%%%%% UNION UPCAST %%%%%%%%%%%%%%%%%%%%%%%

% Upcast to union: meter() is a subtype of meter() | foot()
-spec union_upcast_01(meter()) -> meter() | foot().
union_upcast_01(X) -> X.

% Same through a polymorphic call: should pass
-spec union_upcast_02(meter()) -> meter() | foot().
union_upcast_02(X) -> nominal_id(X).

% Case returning different nominals into a union return type: should pass
-spec union_upcast_case_01(boolean(), integer()) -> meter() | foot().
union_upcast_case_01(true, X) -> structural_to_nominal_01(X);
union_upcast_case_01(false, X) -> structural_to_nominal_foot(X).

-spec structural_to_nominal_foot(integer()) -> foot().
structural_to_nominal_foot(X) -> X.

% Tuple with nominal inside a union with non-tuple: should fail
% {meter()} is structurally incompatible with nil, so the checker must
% skip nil and check against {foot()} where the nominal conflict is.
-spec union_tuple_01_fail({meter()}) -> nil | {foot()}.
union_tuple_01_fail(X) -> X.

% Same structure, same nominal: should pass
-spec union_tuple_02({meter()}) -> nil | {meter()}.
union_tuple_02(X) -> X.

% List with nominal inside a union with non-list: should fail
-spec union_list_01_fail([meter()]) -> ok | [foot()].
union_list_01_fail(X) -> X.

%%%%%%%%%%%%%%%%%%%%%%%% ALIAS UNFOLDING %%%%%%%%%%%%%%%%%%%%%%%

% Named alias hides nominal conflict: should fail
-type meter_foot_pair() :: {meter(), foot()}.

-spec alias_unfold_01_fail(meter_foot_pair()) -> {foot(), meter()}.
alias_unfold_01_fail(X) -> X.

% Named alias on RHS with swapped nominals: should fail
-spec alias_unfold_02_fail({foot(), meter()}) -> meter_foot_pair().
alias_unfold_02_fail(X) -> X.

% Named alias wrapping a list of nominals: should fail
-type meter_list() :: [meter()].

-spec alias_unfold_04_fail(meter_list()) -> [foot()].
alias_unfold_04_fail(X) -> X.

% Same nominal through alias: should pass
-spec alias_unfold_05(meter_list()) -> [meter()].
alias_unfold_05(X) -> X.

% Both sides aliased, same structure: should pass
-spec alias_unfold_06(meter_foot_pair()) -> meter_foot_pair().
alias_unfold_06(X) -> X.

% Alias vs alias with different nominals: should fail
-type foot_meter_pair() :: {foot(), meter()}.

-spec alias_unfold_07_fail(meter_foot_pair()) -> foot_meter_pair().
alias_unfold_07_fail(X) -> X.

% Nested alias: should fail
-type wrapped_meter() :: wrapper(meter()).

-spec alias_unfold_08_fail(wrapped_meter()) -> wrapper(foot()).
alias_unfold_08_fail(X) -> X.

%%%%%%%%%%%%%%%%%%%%%%%% MAP TYPES %%%%%%%%%%%%%%%%%%%%%%%

% Map value nominal conflict: should fail
-spec map_01_fail(#{atom() => meter()}) -> #{atom() => foot()}.
map_01_fail(X) -> X.

% Same nominal in map: should pass
-spec map_02(#{atom() => meter()}) -> #{atom() => meter()}.
map_02(X) -> X.

% Map key nominal conflict: should fail
-spec map_03_fail(#{meter() => atom()}) -> #{foot() => atom()}.
map_03_fail(X) -> X.

%%%%%%%%%%%%%%%%%%%%%%%% CONS / LIST TYPES %%%%%%%%%%%%%%%%%%%%%%%

% Cons with nominal head conflict: should fail
-spec cons_01_fail([meter(), ...]) -> [foot(), ...].
cons_01_fail(X) -> X.

% Same nominal in cons: should pass
-spec cons_02([meter(), ...]) -> [meter(), ...].
cons_02(X) -> X.

% List with union: meter() <: integer() so this should pass
-spec cons_03([meter() | integer()]) -> [foot() | integer()].
cons_03(X) -> X.

% Improper list with nominal conflict: should fail
-spec cons_04_fail(nonempty_improper_list(meter(), integer())) -> nonempty_improper_list(foot(), integer()).
cons_04_fail(X) -> X.

%%%%%%%%%%%%%%%%%%%%%%%% DERIVED NOMINAL TYPES %%%%%%%%%%%%%%%%%%%%%%%

% Derived nominal: container's body IS state (another nominal)
-nominal state() :: integer().
-nominal container() :: state().

% Derived nominal through identity: should pass
% container() <: state() because container() :: state()
-spec derived_01(container()) -> state().
derived_01(X) -> X.

% Reverse direction: state() <: container() holds because
% container() derives from state() (container's body contains state).
-spec derived_02(state()) -> container().
derived_02(X) -> X.

% Derived nominal used in function call: should pass
-spec process_state(state()) -> integer().
process_state(X) -> X.

-spec derived_03(container()) -> integer().
derived_03(X) -> process_state(X).

% Nominal whose body is a union containing another nominal
% alg() :: builtin_alg() | atom()
-nominal builtin_alg() :: exsss | exrop | exs64.
-nominal alg() :: builtin_alg() | atom().

% builtin_alg value used where alg is expected: should pass
% because alg() derives from builtin_alg() (alg's body contains builtin_alg)
-spec derived_04(builtin_alg()) -> alg().
derived_04(X) -> X.

% alg value used where builtin_alg is expected: should fail
% alg() can be an atom() which is not a builtin_alg()
-spec derived_05_fail(alg()) -> builtin_alg().
derived_05_fail(X) -> X.

%%%%%%%%%%%%%%%%%%%%%%%% CONTRAVARIANT POSITIONS (FUNCTION ARGS) %%%%%%%%%%%%%%%%%%%%%%%

-spec contra_01_fail(fun((foot()) -> integer())) -> fun((meter()) -> integer()).
contra_01_fail(F) -> F.

% container() <: state() holds (container derives from state), so contravariance is satisfied
-spec contra_02(fun((state()) -> integer())) -> fun((container()) -> integer()).
contra_02(F) -> F.

% state() <: container() holds (container derives from state), so contravariance is satisfied
-spec contra_03(fun((container()) -> integer())) -> fun((state()) -> integer()).
contra_03(F) -> F.

%%%%%%%%%%%%%%%%%%%%%%%% NEGATION WITH NOMINALS %%%%%%%%%%%%%%%%%%%%%%%

% Nominal hidden inside negation: should fail
% meter() & ¬foot() forces the checker to look inside the negation.
% meter() is not compatible with foot() regardless of negation.
-spec negation_01_fail(etylizer:without(integer(), foot())) -> etylizer:without(integer(), meter()).
negation_01_fail(X) -> X.

% Same nominal in negation: should pass
-spec negation_02(etylizer:without(integer(), meter())) -> etylizer:without(integer(), meter()).
negation_02(X) -> X.

%%%%%%%%%%%%%%%%%%%%%%%% NESTED ALIAS UNFOLDING %%%%%%%%%%%%%%%%%%%%%%%

% Non-nominal aliases hiding nominal types at various nesting depths.
% These test that the nominal checker detects conflicts through
% chains of non-nominal type aliases.

% 2-level: a() -> b() -> meter()
-type hide1_meter() :: meter().
-type hide2_meter() :: hide1_meter().

-spec nested_alias_2_fail(hide2_meter()) -> foot().
nested_alias_2_fail(X) -> X.

% 3-level: a() -> b() -> c() -> meter()
-type hide3_meter() :: hide2_meter().

-spec nested_alias_3_fail(hide3_meter()) -> foot().
nested_alias_3_fail(X) -> X.

% 4-level: a() -> b() -> c() -> d() -> meter()
-type hide4_meter() :: hide3_meter().

-spec nested_alias_4_fail(hide4_meter()) -> foot().
nested_alias_4_fail(X) -> X.

% Both sides hidden behind aliases: should fail
-type hide1_foot() :: foot().
-type hide2_foot() :: hide1_foot().

-spec nested_alias_both_fail(hide2_meter()) -> hide2_foot().
nested_alias_both_fail(X) -> X.

%%%%%%%%%%%%%%%%%%%%%%%% INTERACTION WITH INTERSECTIONS %%%%%%%%%%%%%%%%%%%%%%%

-nominal tagged_meter() :: {unit, integer()}.
-nominal tagged_foot() :: {unit, float()}.

-spec nominal_tagged_01 
    (tagged_meter()) -> tagged_meter();
    (tagged_foot()) -> tagged_foot().
nominal_tagged_01(X) ->
    case X of
        {unit, Z} when is_integer(Z) -> {unit, Z};
        {unit, Z} when is_float(Z) -> {unit, Z}
    end.

-spec nominal_tagged_02
    (tagged_meter()) -> tagged_meter();
    (tagged_foot()) -> tagged_foot().
nominal_tagged_02(X) ->
    nominal_tagged_01(X).

%%%%%%%%%%%%%%%%%%%%%%%% INTERSECTIONS WITH NOMINALS %%%%%%%%%%%%%%%%%%%%%%%

% RHS intersection: nominal T1 <: structural & nominal T2
% meter() <: integer() & foot() should fail because meter() and foot() are incompatible
-spec inter_rhs_01_fail(meter()) -> etylizer:intersection(integer(), foot()).
inter_rhs_01_fail(X) -> X.

% RHS intersection: same nominal on both sides should pass
% meter() <: integer() & meter()
-spec inter_rhs_02(meter()) -> etylizer:intersection(integer(), meter()).
inter_rhs_02(X) -> X.

% RHS intersection: two different nominals should fail
% meter() <: meter() & foot() — meter() is not foot()
-spec inter_rhs_03_fail(meter()) -> etylizer:intersection(meter(), foot()).
inter_rhs_03_fail(X) -> X.

% RHS intersection: purely structural should pass
-spec inter_rhs_04(meter()) -> etylizer:intersection(integer(), number()).
inter_rhs_04(X) -> X.

% LHS intersection: nominal in intersection vs different nominal should fail
% (meter() & integer()) <: foot()
-spec inter_lhs_01_fail(etylizer:intersection(meter(), integer())) -> foot().
inter_lhs_01_fail(X) -> X.

% LHS intersection: nominal in intersection vs same nominal should pass
-spec inter_lhs_02(etylizer:intersection(meter(), integer())) -> meter().
inter_lhs_02(X) -> X.

% LHS intersection: structural should pass
-spec inter_lhs_03(etylizer:intersection(meter(), integer())) -> integer().
inter_lhs_03(X) -> X.

%%%%%%%%%%%%%%%%%%%%%%%% MU (RECURSIVE) TYPES WITH NOMINALS %%%%%%%%%%%%%%%%%%%%%%%

% Recursive list of meters passed as recursive list of feet: should fail
-spec mu_01_fail(etylizer:mu(nil | {meter(), etylizer:mu_var()})) ->
    etylizer:mu(nil | {foot(), etylizer:mu_var()}).
mu_01_fail(X) -> X.

% Same nominal in recursive type: should pass
-spec mu_02(etylizer:mu(nil | {meter(), etylizer:mu_var()})) ->
    etylizer:mu(nil | {meter(), etylizer:mu_var()}).
mu_02(X) -> X.

% Recursive type with nominal vs structural: should pass
-spec mu_03(etylizer:mu(nil | {meter(), etylizer:mu_var()})) ->
    etylizer:mu(nil | {integer(), etylizer:mu_var()}).
mu_03(nil) -> nil;
mu_03({X, Rest}) -> {X, mu_03(Rest)}.
