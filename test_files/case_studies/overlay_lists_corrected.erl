-module(overlay_lists_corrected).
-compile([export_all, nowarn_export_all]).

% Corrected specs of lists.erl: calls use them, the functions are checked against
% these and their specs upstream.

% OTP: ([T], term()) -> [T], the tail is not in the result type and non-emptiness is lost
-spec 'lists:reverse'([], Tail) -> Tail;
                     (nonempty_list(T), [U]) -> nonempty_list(T | U);
                     (list(T), nonempty_list(U)) -> nonempty_list(T | U);
                     (list(T), [U]) -> list(T | U).
'lists:reverse'(_, _) -> error(overlay).

% OTP: ([T]) -> [T], loses non-emptiness, which keysort_1/5 needs
-spec 'lists:reverse'([]) -> [];
                     (nonempty_list(T)) -> nonempty_list(T).
'lists:reverse'(_) -> error(overlay).

% OTP: fun((A, B) -> boolean()): ufmerge2_1/6 and rufmerge2_2/6 also call Fun(B, A)
-spec 'lists:umerge'(fun((A | B, A | B) -> boolean()), [A], [B]) -> [A | B].
'lists:umerge'(_, _, _) -> error(overlay).
-spec 'lists:rumerge'(fun((A | B, A | B) -> boolean()), [A], [B]) -> [A | B].
'lists:rumerge'(_, _, _) -> error(overlay).

% OTP: AccIn, AccOut, Acc0 and Acc1 :: term() are independent type variables
-spec 'lists:foldl'(fun((T, Acc) -> Acc), Acc, [T]) -> Acc.
'lists:foldl'(_, _, _) -> error(overlay).

-spec 'lists:foldr'(fun((T, Acc) -> Acc), Acc, [T]) -> Acc.
'lists:foldr'(_, _, _) -> error(overlay).

-spec 'lists:mapfoldl'(fun((A, Acc) -> {B, Acc}), Acc, [A]) -> {[B], Acc}.
'lists:mapfoldl'(_, _, _) -> error(overlay).
-spec 'lists:mapfoldr'(fun((A, Acc) -> {B, Acc}), Acc, [A]) -> {[B], Acc}.
'lists:mapfoldr'(_, _, _) -> error(overlay).
