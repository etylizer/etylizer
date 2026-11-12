-module(overlay_lists).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

% Specs for the functions of lists.erl that have none upstream. The merge helpers
% return non-empty lists; key sorts work on [tuple()], a key is term(); D arguments
% are dummies, HdM can be the improper sentinel [H2 | H3].

-spec 'lists:nth_1'(pos_integer(), [T]) -> T.
'lists:nth_1'(_, _) -> error(overlay).
-spec 'lists:nthtail_1'(pos_integer(), [T]) -> [T].
'lists:nthtail_1'(_, _) -> error(overlay).
-spec 'lists:last'(T, [T]) -> T.
'lists:last'(_, _) -> error(overlay).
-spec 'lists:seq_loop'(non_neg_integer(), integer(), [integer()]) -> [integer()].
'lists:seq_loop'(_, _, _) -> error(overlay).
-spec 'lists:seq_loop'(non_neg_integer(), integer(), integer(), [integer()]) -> [integer()].
'lists:seq_loop'(_, _, _, _) -> error(overlay).
-spec 'lists:sum'([number()], number()) -> number().
'lists:sum'(_, _) -> error(overlay).
-spec 'lists:duplicate'(non_neg_integer(), T, [T]) -> [T].
'lists:duplicate'(_, _, _) -> error(overlay).
-spec 'lists:min'([T], T) -> T.
'lists:min'(_, _) -> error(overlay).
-spec 'lists:max'([T], T) -> T.
'lists:max'(_, _) -> error(overlay).
-spec 'lists:sublist_2'([T], non_neg_integer()) -> [T].
'lists:sublist_2'(_, _) -> error(overlay).
-spec 'lists:unzip'([{A, B}], [A], [B]) -> {[A], [B]}.
'lists:unzip'(_, _, _) -> error(overlay).
-spec 'lists:unzip3'([{A, B, C}], [A], [B], [C]) -> {[A], [B], [C]}.
'lists:unzip3'(_, _, _, _) -> error(overlay).
-spec 'lists:sort_1'(T, [T], [T, ...]) -> [T].
'lists:sort_1'(_, _, _) -> error(overlay).
-spec 'lists:thing_to_list'(atom() | integer() | float() | string()) -> string().
'lists:thing_to_list'(_) -> error(overlay).
-spec 'lists:do_flatten'(list(), list()) -> list().
'lists:do_flatten'(_, _) -> error(overlay).
-spec 'lists:flatlength'(list(), non_neg_integer()) -> non_neg_integer().
'lists:flatlength'(_, _) -> error(overlay).
-spec 'lists:keydelete3'(term(), pos_integer(), [tuple()]) -> [tuple()].
'lists:keydelete3'(_, _, _) -> error(overlay).
-spec 'lists:keyreplace3'(term(), pos_integer(), [tuple()], tuple()) -> [tuple()].
'lists:keyreplace3'(_, _, _, _) -> error(overlay).
-spec 'lists:keytake'(term(), pos_integer(), [tuple()], [tuple()]) -> {value, tuple(), [tuple()]} | false.
'lists:keytake'(_, _, _, _) -> error(overlay).
-spec 'lists:keystore2'(term(), pos_integer(), [tuple()], tuple()) -> [tuple(), ...].
'lists:keystore2'(_, _, _, _) -> error(overlay).
-spec 'lists:keysort_1'(pos_integer(), tuple(), term(), [tuple()], [tuple(), ...]) -> [tuple()].
'lists:keysort_1'(_, _, _, _, _) -> error(overlay).
-spec 'lists:keymerge_1'(pos_integer(), [tuple()], [tuple()]) -> [tuple()].
'lists:keymerge_1'(_, _, _) -> error(overlay).
-spec 'lists:rkeymerge_1'(pos_integer(), [tuple()], [tuple()]) -> [tuple()].
'lists:rkeymerge_1'(_, _, _) -> error(overlay).
-spec 'lists:ukeysort_1'(pos_integer(), tuple(), term(), [tuple()]) -> [tuple()].
'lists:ukeysort_1'(_, _, _, _) -> error(overlay).
-spec 'lists:ukeymerge_1'(pos_integer(), [tuple()], [tuple()]) -> [tuple()].
'lists:ukeymerge_1'(_, _, _) -> error(overlay).
-spec 'lists:rukeymerge_1'(pos_integer(), [tuple()], [tuple()]) -> [tuple()].
'lists:rukeymerge_1'(_, _, _) -> error(overlay).
-spec 'lists:enumerate_1'(integer(), integer(), [T]) -> [{integer(), T}].
'lists:enumerate_1'(_, _, _) -> error(overlay).
-spec 'lists:merge_1'(fun((A, B) -> boolean()), [A], [B]) -> [A | B].
'lists:merge_1'(_, _, _) -> error(overlay).
-spec 'lists:rmerge_1'(fun((A, B) -> boolean()), [A], [B]) -> [A | B].
'lists:rmerge_1'(_, _, _) -> error(overlay).
-spec 'lists:usort_1'(fun((T, T) -> boolean()), T, [T, ...]) -> [T].
'lists:usort_1'(_, _, _) -> error(overlay).
-spec 'lists:umerge_1'(fun((T, T) -> boolean()), [T], [T]) -> [T].
'lists:umerge_1'(_, _, _) -> error(overlay).
-spec 'lists:rumerge_1'(fun((T, T) -> boolean()), [T], [T]) -> [T].
'lists:rumerge_1'(_, _, _) -> error(overlay).
-spec 'lists:usort_1'(T, [T]) -> [T].
'lists:usort_1'(_, _) -> error(overlay).
-spec 'lists:all_1'(fun((T) -> boolean()), [T]) -> boolean().
'lists:all_1'(_, _) -> error(overlay).
-spec 'lists:any_1'(fun((T) -> boolean()), [T]) -> boolean().
'lists:any_1'(_, _) -> error(overlay).
-spec 'lists:map_1'(fun((A) -> B), [A]) -> [B].
'lists:map_1'(_, _) -> error(overlay).
-spec 'lists:flatmap_1'(fun((A) -> [B]), [A]) -> [B].
'lists:flatmap_1'(_, _) -> error(overlay).
-spec 'lists:foldl_1'(fun((T, Acc) -> Acc), Acc, [T]) -> Acc.
'lists:foldl_1'(_, _, _) -> error(overlay).
-spec 'lists:foldr_1'(fun((T, Acc) -> Acc), Acc, [T]) -> Acc.
'lists:foldr_1'(_, _, _) -> error(overlay).
-spec 'lists:partition_1'(fun((T) -> boolean()), [T], [T], [T]) -> {[T], [T]}.
'lists:partition_1'(_, _, _, _) -> error(overlay).
-spec 'lists:filtermap_1'(fun((E) -> boolean() | {true, V}), [E]) -> [E | V].
'lists:filtermap_1'(_, _) -> error(overlay).
-spec 'lists:foreach_1'(fun((T) -> term()), [T]) -> ok.
'lists:foreach_1'(_, _) -> error(overlay).
-spec 'lists:mapfoldl_1'(fun((A, Acc) -> {B, Acc}), Acc, [A]) -> {[B], Acc}.
'lists:mapfoldl_1'(_, _, _) -> error(overlay).
-spec 'lists:mapfoldr_1'(fun((A, Acc) -> {B, Acc}), Acc, [A]) -> {[B], Acc}.
'lists:mapfoldr_1'(_, _, _) -> error(overlay).
-spec 'lists:takewhile_1'(fun((T) -> boolean()), [T]) -> [T].
'lists:takewhile_1'(_, _) -> error(overlay).
-spec 'lists:dropwhile_1'(fun((T) -> boolean()), [T]) -> [T].
'lists:dropwhile_1'(_, _) -> error(overlay).
-spec 'lists:search_1'(fun((T) -> boolean()), [T]) -> {value, T} | false.
'lists:search_1'(_, _) -> error(overlay).
-spec 'lists:splitwith_1'(fun((T) -> boolean()), [T], [T]) -> {[T], [T]}.
'lists:splitwith_1'(_, _, _) -> error(overlay).
-spec 'lists:split'(non_neg_integer(), [T], [T]) -> {[T], [T]} | badarg.
'lists:split'(_, _, _) -> error(overlay).
-spec 'lists:join_prepend'(T, [T]) -> [T].
'lists:join_prepend'(_, _) -> error(overlay).
-spec 'lists:uniq_1'([T], #{term() => true}) -> [T].
'lists:uniq_1'(_, _) -> error(overlay).
-spec 'lists:uniq_2'([T], fun((T) -> term()), #{term() => true}) -> [T].
'lists:uniq_2'(_, _, _) -> error(overlay).

% sort/1, merge/1, merge/2, merge3/3
-spec 'lists:split_1'(T, T, [T], [T], [[T, ...]]) -> [T].
'lists:split_1'(_, _, _, _, _) -> error(overlay).
-spec 'lists:split_1_1'(T, T, [T], [T], [[T, ...]], T) -> [T].
'lists:split_1_1'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:split_2'(T, T, [T], [T], [[T, ...]]) -> [T].
'lists:split_2'(_, _, _, _, _) -> error(overlay).
-spec 'lists:split_2_1'(T, T, [T], [T], [[T, ...]], T) -> [T].
'lists:split_2_1'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:mergel'([[T]], [[T, ...]]) -> [T].
'lists:mergel'(_, _) -> error(overlay).
-spec 'lists:rmergel'([[T, ...]], [[T, ...]]) -> [T].
'lists:rmergel'(_, _) -> error(overlay).
-spec 'lists:merge3_1'([T], [T], T, [T], T, [T]) -> [T, ...].
'lists:merge3_1'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:merge3_2'([T], T, [T], [T], T, [T]) -> [T, ...].
'lists:merge3_2'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:merge3_12'([T], T, T, [T], T, [T], [T]) -> [T, ...].
'lists:merge3_12'(_, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:merge3_12_3'([T], T, T, [T], [T], [T]) -> [T, ...].
'lists:merge3_12_3'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:merge3_21'([T], T, T, [T], T, [T], [T]) -> [T, ...].
'lists:merge3_21'(_, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:merge3_21_3'([T], T, T, [T], [T], [T]) -> [T, ...].
'lists:merge3_21_3'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:rmerge3_1'([T], [T], T, [T], T, [T]) -> [T, ...].
'lists:rmerge3_1'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:rmerge3_2'([T], T, [T], [T], T, [T]) -> [T, ...].
'lists:rmerge3_2'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:rmerge3_12'([T], T, T, [T], T, [T], [T]) -> [T, ...].
'lists:rmerge3_12'(_, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rmerge3_12_3'([T], T, T, [T], [T], [T]) -> [T, ...].
'lists:rmerge3_12_3'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:rmerge3_21'([T], T, T, [T], T, [T], [T]) -> [T, ...].
'lists:rmerge3_21'(_, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rmerge3_21_3'([T], T, T, [T], [T], [T]) -> [T, ...].
'lists:rmerge3_21_3'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:merge2_1'([T], T, [T], [T]) -> [T, ...].
'lists:merge2_1'(_, _, _, _) -> error(overlay).
-spec 'lists:merge2_2'([T], T, [T], [T], T) -> [T, ...].
'lists:merge2_2'(_, _, _, _, _) -> error(overlay).
-spec 'lists:rmerge2_1'([T], T, [T], [T]) -> [T, ...].
'lists:rmerge2_1'(_, _, _, _) -> error(overlay).
-spec 'lists:rmerge2_2'([T], T, [T], [T], T) -> [T, ...].
'lists:rmerge2_2'(_, _, _, _, _) -> error(overlay).

% usort/1, umerge/1, umerge/2, umerge3/3
-spec 'lists:usplit_1'(T, T, [T], [T], [[T, ...]]) -> [T].
'lists:usplit_1'(_, _, _, _, _) -> error(overlay).
-spec 'lists:usplit_1_1'(T, T, [T], [T], [[T, ...]], T) -> [T].
'lists:usplit_1_1'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:usplit_2'(T, T, [T], [T], [[T, ...]]) -> [T].
'lists:usplit_2'(_, _, _, _, _) -> error(overlay).
-spec 'lists:usplit_2_1'(T, T, [T], [T], [[T, ...]], T) -> [T].
'lists:usplit_2_1'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:umergel'([[T]]) -> [T].
'lists:umergel'(_) -> error(overlay).
-spec 'lists:umergel'([[T]], [[T, ...]], asc | desc) -> [T].
'lists:umergel'(_, _, _) -> error(overlay).
-spec 'lists:rumergel'([[T, ...]], [[T, ...]], asc | desc) -> [T].
'lists:rumergel'(_, _, _) -> error(overlay).
-spec 'lists:umerge3_1'([T], term(), [T], T, [T], [T], T) -> [T, ...].
'lists:umerge3_1'(_, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:umerge3_2'([T], T, [T], term(), [T], [T], T) -> [T, ...].
'lists:umerge3_2'(_, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:umerge3_12'([T], T, [T], T, [T], [T], T, term()) -> [T, ...].
'lists:umerge3_12'(_, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:umerge3_12_3'([T], T, [T], T, [T], [T]) -> [T, ...].
'lists:umerge3_12_3'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:umerge3_21'([T], T, [T], T, [T], [T], T, term()) -> [T, ...].
'lists:umerge3_21'(_, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:umerge3_21_3'([T], T, [T], T, [T], [T]) -> [T, ...].
'lists:umerge3_21_3'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:rumerge3_1'([T], [T], T, [T], [T], T) -> [T, ...].
'lists:rumerge3_1'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:rumerge3_12a'([T], T, [T], T, [T], [T], T) -> [T, ...].
'lists:rumerge3_12a'(_, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rumerge3_2'([T], [T], T, [T], [T], T, T) -> [T, ...].
'lists:rumerge3_2'(_, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rumerge3_12b'([T], T, [T], T, [T], [T], T, T) -> [T, ...].
'lists:rumerge3_12b'(_, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rumerge3_12_3'([T], [T], T, [T], [T], T, T) -> [T, ...].
'lists:rumerge3_12_3'(_, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rumerge3_21_3'([T], [T], T, [T], [T], T, T) -> [T, ...].
'lists:rumerge3_21_3'(_, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:umerge2_1'([T], [T], [T, ...], term(), T) -> [T, ...].
'lists:umerge2_1'(_, _, _, _, _) -> error(overlay).
-spec 'lists:umerge2_2'([T], [T], [T], T) -> [T, ...].
'lists:umerge2_2'(_, _, _, _) -> error(overlay).
-spec 'lists:rumerge2_1'([T], [T], [T], T) -> [T, ...].
'lists:rumerge2_1'(_, _, _, _) -> error(overlay).
-spec 'lists:rumerge2_2'([T], [T], [T], T, T) -> [T, ...].
'lists:rumerge2_2'(_, _, _, _, _) -> error(overlay).

% keysort/2, keymerge/3
-spec 'lists:keysplit_1'(pos_integer(), tuple(), term(), tuple(), term(), [tuple()], [tuple()], [[tuple(), ...]]) -> [tuple()].
'lists:keysplit_1'(_, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:keysplit_1_1'(pos_integer(), tuple(), term(), tuple(), term(), term(), [tuple()], [[tuple(), ...]], tuple(), [tuple()]) -> [tuple()].
'lists:keysplit_1_1'(_, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:keysplit_2'(pos_integer(), tuple(), term(), tuple(), term(), [tuple()], [tuple()], [[tuple(), ...]]) -> [tuple()].
'lists:keysplit_2'(_, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:keysplit_2_1'(pos_integer(), tuple(), term(), tuple(), term(), term(), [tuple()], [[tuple(), ...]], tuple(), [tuple()]) -> [tuple()].
'lists:keysplit_2_1'(_, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:keymergel'(pos_integer(), [[tuple(), ...]], [[tuple(), ...]], asc | desc) -> [tuple()].
'lists:keymergel'(_, _, _, _) -> error(overlay).
-spec 'lists:rkeymergel'(pos_integer(), [[tuple(), ...]], [[tuple(), ...]], asc | desc) -> [tuple()].
'lists:rkeymergel'(_, _, _, _) -> error(overlay).
-spec 'lists:keymerge3_1'(pos_integer(), [tuple()], [tuple()], term(), term(), tuple(), [tuple()], term(), tuple(), [tuple()]) -> [tuple(), ...].
'lists:keymerge3_1'(_, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:keymerge3_2'(pos_integer(), term(), tuple(), [tuple()], [tuple()], [tuple()], term(), term(), tuple(), [tuple()]) -> [tuple(), ...].
'lists:keymerge3_2'(_, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:keymerge3_12'(pos_integer(), term(), tuple(), [tuple()], term(), tuple(), [tuple()], term(), tuple(), [tuple()], [tuple()], term()) -> [tuple(), ...].
'lists:keymerge3_12'(_, _, _, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:keymerge3_12_3'(pos_integer(), term(), tuple(), [tuple()], term(), tuple(), [tuple()], [tuple()], [tuple()]) -> [tuple(), ...].
'lists:keymerge3_12_3'(_, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:keymerge3_21'(pos_integer(), term(), tuple(), [tuple()], term(), tuple(), [tuple()], term(), tuple(), [tuple()], [tuple()], term()) -> [tuple(), ...].
'lists:keymerge3_21'(_, _, _, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:keymerge3_21_3'(pos_integer(), term(), tuple(), [tuple()], term(), tuple(), [tuple()], [tuple()], [tuple()]) -> [tuple(), ...].
'lists:keymerge3_21_3'(_, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rkeymerge3_1'(pos_integer(), [tuple()], [tuple()], term(), term(), tuple(), [tuple()], term(), tuple(), [tuple()]) -> [tuple(), ...].
'lists:rkeymerge3_1'(_, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rkeymerge3_2'(pos_integer(), term(), tuple(), [tuple()], [tuple()], [tuple()], term(), term(), tuple(), [tuple()]) -> [tuple(), ...].
'lists:rkeymerge3_2'(_, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rkeymerge3_12'(pos_integer(), term(), tuple(), [tuple()], term(), tuple(), [tuple()], term(), tuple(), [tuple()], [tuple()], term()) -> [tuple(), ...].
'lists:rkeymerge3_12'(_, _, _, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rkeymerge3_12_3'(pos_integer(), term(), tuple(), [tuple()], term(), tuple(), [tuple()], [tuple()], [tuple()]) -> [tuple(), ...].
'lists:rkeymerge3_12_3'(_, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rkeymerge3_21'(pos_integer(), term(), tuple(), [tuple()], term(), tuple(), [tuple()], term(), tuple(), [tuple()], [tuple()], term()) -> [tuple(), ...].
'lists:rkeymerge3_21'(_, _, _, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rkeymerge3_21_3'(pos_integer(), term(), tuple(), [tuple()], term(), tuple(), [tuple()], [tuple()], [tuple()]) -> [tuple(), ...].
'lists:rkeymerge3_21_3'(_, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:keymerge2_1'(pos_integer(), [tuple()], term(), tuple(), [tuple()], [tuple()]) -> [tuple(), ...].
'lists:keymerge2_1'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:keymerge2_2'(pos_integer(), [tuple()], term(), tuple(), [tuple()], [tuple()], tuple()) -> [tuple(), ...].
'lists:keymerge2_2'(_, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rkeymerge2_1'(pos_integer(), [tuple()], term(), tuple(), [tuple()], [tuple()]) -> [tuple(), ...].
'lists:rkeymerge2_1'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:rkeymerge2_2'(pos_integer(), term(), [tuple()], tuple(), [tuple()], [tuple()], tuple()) -> [tuple(), ...].
'lists:rkeymerge2_2'(_, _, _, _, _, _, _) -> error(overlay).

% ukeysort/2, ukeymerge/3
-spec 'lists:ukeysplit_1'(pos_integer(), tuple(), term(), tuple(), term(), [tuple()], [tuple()], [[tuple(), ...]]) -> [tuple()].
'lists:ukeysplit_1'(_, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:ukeysplit_1_1'(pos_integer(), tuple(), term(), tuple(), term(), [tuple()], [tuple()], [[tuple(), ...]], tuple(), term()) -> [tuple()].
'lists:ukeysplit_1_1'(_, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:ukeysplit_2'(pos_integer(), tuple(), term(), [tuple()], [tuple(), ...]) -> [tuple()].
'lists:ukeysplit_2'(_, _, _, _, _) -> error(overlay).
-spec 'lists:ukeymergel'(pos_integer(), [[tuple(), ...]], [[tuple(), ...]]) -> [tuple()].
'lists:ukeymergel'(_, _, _) -> error(overlay).
-spec 'lists:rukeymergel'(pos_integer(), [[tuple(), ...]], [[tuple(), ...]]) -> [tuple()].
'lists:rukeymergel'(_, _, _) -> error(overlay).
-spec 'lists:ukeymerge3_1'(pos_integer(), [tuple()], term(), term(), term(), tuple(), [tuple()], [tuple()], term(), tuple(), [tuple()]) -> [tuple(), ...].
'lists:ukeymerge3_1'(_, _, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:ukeymerge3_2'(pos_integer(), term(), [tuple()], tuple(), [tuple()], term(), term(), [tuple()], term(), tuple(), [tuple()]) -> [tuple(), ...].
'lists:ukeymerge3_2'(_, _, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:ukeymerge3_12'(pos_integer(), term(), [tuple()], tuple(), term(), tuple(), [tuple()], term(), tuple(), [tuple()], [tuple()], term(), term()) -> [tuple(), ...].
'lists:ukeymerge3_12'(_, _, _, _, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:ukeymerge3_12_3'(pos_integer(), term(), [tuple()], tuple(), term(), tuple(), [tuple()], [tuple()], [tuple()]) -> [tuple(), ...].
'lists:ukeymerge3_12_3'(_, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:ukeymerge3_21'(pos_integer(), term(), [tuple()], tuple(), term(), tuple(), [tuple()], term(), tuple(), [tuple()], [tuple()], term(), term()) -> [tuple(), ...].
'lists:ukeymerge3_21'(_, _, _, _, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:ukeymerge3_21_3'(pos_integer(), term(), [tuple()], tuple(), term(), tuple(), [tuple()], [tuple()], [tuple()]) -> [tuple(), ...].
'lists:ukeymerge3_21_3'(_, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rukeymerge3_1'(pos_integer(), [tuple()], term(), term(), term(), tuple(), [tuple()], [tuple()], term(), tuple(), [tuple()]) -> [tuple(), ...].
'lists:rukeymerge3_1'(_, _, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rukeymerge3_12a'(pos_integer(), term(), tuple(), [tuple()], term(), tuple(), [tuple()], term(), tuple(), [tuple()], [tuple()]) -> [tuple(), ...].
'lists:rukeymerge3_12a'(_, _, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rukeymerge3_21a'(pos_integer(), term(), tuple(), [tuple()], term(), tuple(), [tuple()], term(), tuple(), [tuple()], [tuple()], term(), term()) -> [tuple(), ...].
'lists:rukeymerge3_21a'(_, _, _, _, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rukeymerge3_2'(pos_integer(), term(), tuple(), [tuple()], [tuple()], tuple(), term(), [tuple()], term(), tuple(), [tuple()]) -> [tuple(), ...].
'lists:rukeymerge3_2'(_, _, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rukeymerge3_12b'(pos_integer(), term(), tuple(), [tuple()], term(), tuple(), [tuple()], term(), tuple(), [tuple()], [tuple()], tuple()) -> [tuple(), ...].
'lists:rukeymerge3_12b'(_, _, _, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rukeymerge3_21b'(pos_integer(), term(), tuple(), [tuple()], term(), tuple(), [tuple()], term(), tuple(), [tuple()], [tuple()], tuple()) -> [tuple(), ...].
'lists:rukeymerge3_21b'(_, _, _, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rukeymerge3_12_3'(pos_integer(), term(), tuple(), [tuple()], term(), tuple(), [tuple()], [tuple()], term(), tuple(), [tuple()]) -> [tuple(), ...].
'lists:rukeymerge3_12_3'(_, _, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:rukeymerge3_21_3'(pos_integer(), term(), tuple(), [tuple()], term(), tuple(), [tuple()], [tuple()], term(), tuple(), [tuple()]) -> [tuple(), ...].
'lists:rukeymerge3_21_3'(_, _, _, _, _, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:ukeymerge2_1'(pos_integer(), [tuple()], term(), term(), [tuple()], [tuple(), ...], tuple()) -> [tuple(), ...].
'lists:ukeymerge2_1'(_, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:ukeymerge2_2'(pos_integer(), [tuple()], term(), tuple(), [tuple()], [tuple()]) -> [tuple(), ...].
'lists:ukeymerge2_2'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:rukeymerge2_1'(pos_integer(), [tuple()], term(), [tuple()], [tuple()], tuple()) -> [tuple(), ...].
'lists:rukeymerge2_1'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:rukeymerge2_2'(pos_integer(), [tuple()], term(), [tuple()], [tuple()], term(), tuple(), tuple()) -> [tuple(), ...].
'lists:rukeymerge2_2'(_, _, _, _, _, _, _, _) -> error(overlay).

% sort/2, merge/3
-spec 'lists:fsplit_1'(T, T, fun((T, T) -> boolean()), [T], [T], [[T, ...]]) -> [T].
'lists:fsplit_1'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:fsplit_1_1'(T, T, fun((T, T) -> boolean()), [T], [T], [[T, ...]], T) -> [T].
'lists:fsplit_1_1'(_, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:fsplit_2'(T, T, fun((T, T) -> boolean()), [T], [T], [[T, ...]]) -> [T].
'lists:fsplit_2'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:fsplit_2_1'(T, T, fun((T, T) -> boolean()), [T], [T], [[T, ...]], T) -> [T].
'lists:fsplit_2_1'(_, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:fmergel'([[T, ...]], [[T, ...]], fun((T, T) -> boolean()), asc | desc) -> [T].
'lists:fmergel'(_, _, _, _) -> error(overlay).
-spec 'lists:rfmergel'([[T, ...]], [[T, ...]], fun((T, T) -> boolean()), asc | desc) -> [T].
'lists:rfmergel'(_, _, _, _) -> error(overlay).
-spec 'lists:fmerge2_1'([A], B, fun((A, B) -> boolean()), [B], [A | B]) -> [A | B, ...].
'lists:fmerge2_1'(_, _, _, _, _) -> error(overlay).
-spec 'lists:fmerge2_2'(A, [A], fun((A, B) -> boolean()), [B], [A | B]) -> [A | B, ...].
'lists:fmerge2_2'(_, _, _, _, _) -> error(overlay).
-spec 'lists:rfmerge2_1'([A], B, fun((A, B) -> boolean()), [B], [A | B]) -> [A | B, ...].
'lists:rfmerge2_1'(_, _, _, _, _) -> error(overlay).
-spec 'lists:rfmerge2_2'(A, [A], fun((A, B) -> boolean()), [B], [A | B]) -> [A | B, ...].
'lists:rfmerge2_2'(_, _, _, _, _) -> error(overlay).

% usort/2, umerge/3
-spec 'lists:ufsplit_1'(T, T, fun((T, T) -> boolean()), [T], [T], [[T, ...]]) -> [T].
'lists:ufsplit_1'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:ufsplit_1_1'(T, T, fun((T, T) -> boolean()), [T], [T], [[T, ...]], T) -> [T].
'lists:ufsplit_1_1'(_, _, _, _, _, _, _) -> error(overlay).
-spec 'lists:ufsplit_2'(T, [T], fun((T, T) -> boolean()), [T, ...]) -> [T].
'lists:ufsplit_2'(_, _, _, _) -> error(overlay).
-spec 'lists:ufmergel'([[T, ...]], [[T, ...]], fun((T, T) -> boolean())) -> [T].
'lists:ufmergel'(_, _, _) -> error(overlay).
-spec 'lists:rufmergel'([[T, ...]], [[T, ...]], fun((T, T) -> boolean())) -> [T].
'lists:rufmergel'(_, _, _) -> error(overlay).
-spec 'lists:ufmerge2_1'([T], T, fun((T, T) -> boolean()), [T], [T, ...], T) -> [T, ...].
'lists:ufmerge2_1'(_, _, _, _, _, _) -> error(overlay).
-spec 'lists:ufmerge2_2'(T, [T], fun((T, T) -> boolean()), [T], [T]) -> [T, ...].
'lists:ufmerge2_2'(_, _, _, _, _) -> error(overlay).
-spec 'lists:rufmerge2_1'([T], T, fun((T, T) -> boolean()), [T], [T]) -> [T, ...].
'lists:rufmerge2_1'(_, _, _, _, _) -> error(overlay).
-spec 'lists:rufmerge2_2'(T, [T], fun((T, T) -> boolean()), [T], [T], T) -> [T, ...].
'lists:rufmerge2_2'(_, _, _, _, _, _) -> error(overlay).
