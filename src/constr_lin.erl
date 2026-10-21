-module(constr_lin).

% @doc Linear integer facts over program variables and list lengths, collected from
% bindings and guards. They answer whether a list variable can be [] at a case.

-export([empty/0, clause/4, nonempty/2]).
-export_type([t/0]).

-record(lin,
        { facts = [] :: [lin()],
          % variables known to be integers
          ints = [] :: [ast:local_varname()]
        }).
-opaque t() :: #lin{}.
% Sum of Coef * Term + Const >= 0, terms {v, X} and {len, X} are integers
-type lin() :: {#{lin_term() => integer()}, integer()}.
-type lin_term() :: {v | len, ast:local_varname()}.

-spec empty() -> t().
empty() -> #lin{}.

% Facts that hold in a clause body: pattern variables bound to a linear
% scrutinee, then the comparisons of a single guard.
-spec clause(t(), ast:exp(), ast:pat(), [ast:guard()]) -> t().
clause(Fs0, Scrut, Pat, Guards) ->
    Fs1 = case lin_of_exp(Fs0, Scrut) of
              {ok, Lin} ->
                  lists:foldl(fun(V, F) -> add_eq(F#lin{ints = [V | F#lin.ints]}, lin_var(V), Lin) end,
                              Fs0, top_vars(Pat));
              error -> Fs0
          end,
    case Guards of
        [Tests] ->
            Fs2 = lists:foldl(fun guard_ints/2, Fs1, Tests),
            lists:foldl(fun guard_facts/2, Fs2, Tests);
        _ -> Fs1
    end.

-spec top_vars(ast:pat()) -> [ast:local_varname()].
top_vars({var, _, {local_bind, V}}) -> [V];
top_vars({var, _, {local_ref, V}}) -> [V];
top_vars({match, _, P1, P2}) -> top_vars(P1) ++ top_vars(P2);
top_vars(_) -> [].

-spec guard_ints(ast:guard_test(), t()) -> t().
guard_ints({op, _, 'andalso', L, R}, Fs) -> guard_ints(R, guard_ints(L, Fs));
guard_ints({call, _, {var, _, Ref}, [{var, _, {local_ref, V}}]}, Fs)
  when Ref =:= {ref, is_integer, 1}; Ref =:= {qref, erlang, is_integer, 1} ->
    Fs#lin{ints = [V | Fs#lin.ints]};
guard_ints(_, Fs) -> Fs.

-spec guard_facts(ast:guard_test(), t()) -> t().
guard_facts({op, _, 'andalso', L, R}, Fs) -> guard_facts(R, guard_facts(L, Fs));
guard_facts({op, _, Op, L, R}, Fs) ->
    case {lin_of_exp(Fs, L), lin_of_exp(Fs, R)} of
        {{ok, A}, {ok, B}} ->
            case Op of
                '>=' -> add_fact(Fs, lin_sub(A, B));
                '>' -> add_fact(Fs, lin_add(lin_sub(A, B), {#{}, -1}));
                '=<' -> add_fact(Fs, lin_sub(B, A));
                '<' -> add_fact(Fs, lin_add(lin_sub(B, A), {#{}, -1}));
                % both sides are integers, so == is =:=
                _ when Op =:= '=:='; Op =:= '==' -> add_eq(Fs, A, B);
                _ -> Fs
            end;
        _ -> Fs
    end;
guard_facts(_, Fs) -> Fs.

% Integer-valued linear expressions only: literals, integer variables, length/1 of a variable
-spec lin_of_exp(t(), ast:exp()) -> t:opt(lin()).
lin_of_exp(Fs, E) ->
    case E of
        {integer, _, I} -> {ok, {#{}, I}};
        {var, _, {local_ref, V}} ->
            case lists:member(V, Fs#lin.ints) of
                true -> {ok, lin_var(V)};
                false -> error
            end;
        {call, _, {var, _, Ref}, [{var, _, {local_ref, X}}]}
          when Ref =:= {ref, length, 1}; Ref =:= {qref, erlang, length, 1} ->
            {ok, {#{{len, X} => 1}, 0}};
        {op, _, Op, A, B} when Op =:= '+'; Op =:= '-' ->
            case {lin_of_exp(Fs, A), lin_of_exp(Fs, B)} of
                {{ok, LA}, {ok, LB}} when Op =:= '+' -> {ok, lin_add(LA, LB)};
                {{ok, LA}, {ok, LB}} -> {ok, lin_sub(LA, LB)};
                _ -> error
            end;
        {op, _, '-', A} ->
            case lin_of_exp(Fs, A) of
                {ok, LA} -> {ok, lin_scale(LA, -1)};
                error -> error
            end;
        _ -> error
    end.

-spec lin_var(ast:local_varname()) -> lin().
lin_var(V) -> {#{{v, V} => 1}, 0}.

-spec lin_add(lin(), lin()) -> lin().
lin_add({M1, K1}, {M2, K2}) -> {maps:merge_with(fun(_, A, B) -> A + B end, M1, M2), K1 + K2}.

-spec lin_scale(lin(), integer()) -> lin().
lin_scale({M, K}, F) -> {maps:map(fun(_, C) -> C * F end, M), K * F}.

-spec lin_sub(lin(), lin()) -> lin().
lin_sub(A, B) -> lin_add(A, lin_scale(B, -1)).

-spec add_eq(t(), lin(), lin()) -> t().
add_eq(Fs, A, B) -> add_fact(add_fact(Fs, lin_sub(A, B)), lin_sub(B, A)).

% A length is not negative
-spec add_fact(t(), lin()) -> t().
add_fact(Fs = #lin{facts = Facts}, Lin = {M, _}) ->
    Lens = [{#{T => 1}, 0} || T = {len, _} <- maps:keys(M)],
    Fs#lin{facts = lists:usort([Lin | Lens] ++ Facts)}.

% length(V) = 0 contradicts the facts
-spec nonempty(t(), ast:local_varname()) -> boolean().
nonempty(#lin{facts = Facts}, V) ->
    Len = {len, V},
    lists:any(fun({M, _}) -> maps:is_key(Len, M) end, Facts)
        andalso fm_unsat([{#{Len => -1}, 0} | Facts]).

% Fourier-Motzkin elimination with integer tightening; false means unknown
-spec fm_unsat([lin()]) -> boolean().
fm_unsat(Cs) -> fm(lists:map(fun lin_norm/1, Cs)).

% Constant facts K >= 0 are dropped if they hold and refute the set if not
-spec fm([lin()]) -> boolean().
fm(Cs0) ->
    Cs = [C || C = {M, K} <- Cs0, maps:size(M) > 0 orelse K < 0],
    case lists:any(fun({M, _}) -> maps:size(M) =:= 0 end, Cs) of
        true -> true;
        false ->
            case [T || {M, _} <- Cs, T <- maps:keys(M)] of
                [] -> false;
                [T | _] ->
                    {Pos, Neg, Rest} =
                        lists:foldl(
                          fun(C = {M, _}, {P, N, R}) ->
                                  case maps:get(T, M, 0) of
                                      0 -> {P, N, [C | R]};
                                      X when X > 0 -> {[C | P], N, R};
                                      _ -> {P, [C | N], R}
                                  end
                          end, {[], [], []}, Cs),
                    New = [lin_norm(lin_add(lin_scale(CP, -maps:get(T, MN)), lin_scale(CN, maps:get(T, MP))))
                           || CP = {MP, _} <- Pos, CN = {MN, _} <- Neg],
                    fm(Rest ++ New)
            end
    end.

-spec lin_norm(lin()) -> lin().
lin_norm({M0, K}) ->
    M = maps:filter(fun(_, C) -> C =/= 0 end, M0),
    case maps:size(M) of
        0 -> {M, K};
        _ ->
            G = lists:foldl(fun(C, Acc) -> gcd(abs(C), Acc) end, 0, maps:values(M)),
            Q = K div G,
            {maps:map(fun(_, C) -> C div G end, M), case K rem G < 0 of true -> Q - 1; false -> Q end}
    end.

-spec gcd(non_neg_integer(), non_neg_integer()) -> non_neg_integer().
gcd(A, 0) -> A;
gcd(A, B) -> gcd(B, A rem B).
