-module(overlay_otp_etylizer_lib).
-compile([export_all, nowarn_export_all]).

% Library specs for otp_etylizer.study, the corrected specs of lists.study.

% OTP: ([T]) -> [T], loses non-emptiness
-spec 'lists:reverse'([]) -> [];
                     (nonempty_list(T)) -> nonempty_list(T).
'lists:reverse'(_) -> error(overlay).

-spec 'lists:foldl'(fun((T, Acc) -> Acc), Acc, [T]) -> Acc.
'lists:foldl'(_, _, _) -> error(overlay).

-spec 'lists:keyfind'(Key :: term(), N :: pos_integer(), [Tuple]) -> Tuple | false.
'lists:keyfind'(_, _, _) -> error(overlay).

% OTP: Tuple :: tuple(), a bound read as the type
-spec 'lists:keydelete'(term(), pos_integer(), [T]) -> [T].
'lists:keydelete'(_, _, _) -> error(overlay).
-spec 'lists:keyreplace'(term(), pos_integer(), [T], T) -> [T].
'lists:keyreplace'(_, _, _, _) -> error(overlay).

% OTP: (pos_integer(), pos_integer()) -> reference(), atomics:new(1, [{signed, false}]) passes 0
-spec 'erts_internal:atomics_new'(pos_integer(), non_neg_integer()) -> reference().
'erts_internal:atomics_new'(_, _) -> error(overlay).

% OTP: Maximum :: term(), Minimum :: term()
-spec 'erlang:max'(A, B) -> A | B.
'erlang:max'(_, _) -> error(overlay).
-spec 'erlang:min'(A, B) -> A | B.
'erlang:min'(_, _) -> error(overlay).

% OTP: Head :: term()
-spec 'erlang:hd'(nonempty_maybe_improper_list(T, term())) -> T.
'erlang:hd'(_) -> error(overlay).
