%% Library specs for the prometheus case study (prometheus.study): functions of OTP whose spec says too
%% little for the checker, or too much at once. Each spec is true for every call that it admits; none
%% says more than the function does. A result that OTP gives as a type variable bound only in `when`
%% (which fits every type) is term() here.
%% An overlay spec replaces the spec that OTP has. For a function that has no spec in OTP
%% (mnesia_tm:get_info/1, ram_file:open/2, ram_file:get_size/1) the checker takes none from an overlay.
-module(overlay_prometheus_lib).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

%% ---------------------------------------------------------------------------------------------------
%% erlang

%% OTP: (pos_integer(), tuple()) -> term(). The element of a pair and of a tuple of five, the row of a
%% metric family in the tables of the metric modules (prometheus_metric:mf_labels/1 and the like).
-spec 'erlang:element'(2, {_, B}) -> B;
                      (2, {_, B, _, _, _}) -> B;
                      (3, {_, _, C, _, _}) -> C;
                      (4, {_, _, _, D, _}) -> D;
                      (5, {_, _, _, _, E}) -> E;
                      (pos_integer(), tuple()) -> term().
'erlang:element'(_, _) -> error(overlay).

%% the digits and the sign are bytes, OTP says string()
-spec 'erlang:integer_to_list'(integer()) -> [45 | 48..57, ...].
'erlang:integer_to_list'(_) -> error(overlay).

%% OTP has 81 clauses, one or more for each item. With them the check of
%% prometheus_vm_system_info_collector:allocators/0, which calls the function twice, runs into the
%% timeout; with more time it ends after 20 s and accepts the function, wrongly. Here: the items that
%% prometheus asks for, with the results that OTP gives them. For {allocator, Alloc}, where OTP says
%% [_], there are also false and undefined: the documentation has false for an allocator that is
%% disabled and undefined for one that is not known.
-spec 'erlang:system_info'
    (wordsize) -> 4 | 8;
    (scheduler_id | schedulers | schedulers_online | ets_limit | port_limit | process_count | process_limit |
     atom_count | atom_limit) -> pos_integer();
    (dirty_cpu_schedulers | dirty_cpu_schedulers_online | dirty_io_schedulers | port_count | thread_pool_size) ->
        non_neg_integer();
    (logical_processors | logical_processors_available | logical_processors_online) -> unknown | pos_integer();
    (smp_support | threads | time_correction) -> boolean();
    (alloc_util_allocators) -> [atom()];
    ({allocator, atom()}) -> [term()] | false | undefined.
'erlang:system_info'(_) -> error(overlay).

%% OTP has 19 clauses and gives the results with type variables bound in when, {Total, SinceLastCall} when
%% Total :: non_neg_integer(), ..; a match on such a result of an overloaded spec is reported as dead. Here: the
%% items that prometheus asks for, with the results that OTP gives them, the types in place of the variables.
-spec 'erlang:statistics'
    (context_switches) -> {non_neg_integer(), 0};
    (garbage_collection) -> {non_neg_integer(), non_neg_integer(), 0};
    (io) -> {{input, non_neg_integer()}, {output, non_neg_integer()}};
    (microstate_accounting) -> [#{type := atom(), id := non_neg_integer(),
                                  counters := #{atom() => non_neg_integer()}}] | undefined;
    (reductions | runtime | wall_clock) -> {non_neg_integer(), non_neg_integer()};
    (run_queue) -> non_neg_integer();
    (run_queue_lengths_all) -> [non_neg_integer()].
'erlang:statistics'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------------
%% application

%% OTP: {ok, Val} when Val :: term()
-spec 'application:get_env'(atom(), atom()) -> undefined | {ok, term()}.
'application:get_env'(_, _) -> error(overlay).

%% OTP: Val when Val :: term()
-spec 'application:get_env'(atom(), atom(), term()) -> term().
'application:get_env'(_, _, _) -> error(overlay).

-spec 'application:get_key'(atom(), atom()) -> undefined | {ok, term()}.
'application:get_key'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------------
%% ets

%% OTP: [Match] when Match :: term()
-spec 'ets:select'(ets:table(), ets:match_spec()) -> [term()].
'ets:select'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------------
%% lists

%% OTP has five variables for the accumulator and the element, bound only in when
-spec 'lists:foldl'(fun((T, Acc) -> Acc), Acc, [T]) -> Acc.
'lists:foldl'(_, _, _) -> error(overlay).

-spec 'lists:foldr'(fun((T, Acc) -> Acc), Acc, [T]) -> Acc.
'lists:foldr'(_, _, _) -> error(overlay).

%% OTP: [A] -> [B]. A list that is not empty stays so.
-spec 'lists:map'(fun((A) -> B), [A, ...]) -> [B, ...]; (fun((A) -> B), [A]) -> [B].
'lists:map'(_, _) -> error(overlay).

%% OTP says tuple() for the elements
-spec 'lists:keyfind'(term(), pos_integer(), [T]) -> T | false.
'lists:keyfind'(_, _, _) -> error(overlay).

%% OTP: [integer()]. An ascending sequence does not go below its start.
-spec 'lists:seq'(pos_integer(), integer()) -> [pos_integer()];
                 (non_neg_integer(), integer()) -> [non_neg_integer()];
                 (integer(), integer()) -> [integer()].
'lists:seq'(_, _) -> error(overlay).

%% OTP: number(). The sum of the empty list is 0, so a list of floats has to be non-empty for float().
-spec 'lists:sum'([non_neg_integer()]) -> non_neg_integer();
                 ([integer()]) -> integer();
                 ([float(), ...]) -> float();
                 ([number()]) -> number().
'lists:sum'(_) -> error(overlay).

%% OTP: [term()]. The elements of the result are the elements of the deep list that are not lists: for
%% a list of elements and lists of elements when the elements are no lists themselves, and for a list of
%% lists of lists of such elements.
-type deep_term() :: [term() | deep_term()].
-spec 'lists:flatten'([[etylizer:without(A, list())] | etylizer:without(A, list())]) -> [etylizer:without(A, list())];
                     ([[[etylizer:without(A, list())]]]) -> [etylizer:without(A, list())];
                     (deep_term()) -> [term()].
'lists:flatten'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------------
%% proplists

%% OTP: (Key, List) -> List when List :: [term()]. The result has the elements of the list that are left.
-spec 'proplists:delete'(term(), [T]) -> [T].
'proplists:delete'(_, _) -> error(overlay).
