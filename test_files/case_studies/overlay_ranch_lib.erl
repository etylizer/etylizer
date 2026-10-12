%% Library specs for the ranch case study that overlay.erl does not have. Each spec is true for every
%% call of the function; none says more than the function does.
-module(overlay_ranch_lib).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

%% lists: OTP says [tuple()] for the list of the key functions. They pass over an element that is no
%% tuple: the options of a socket hold atoms (inet, inet6, binary).

-spec 'lists:keymember'(Key :: term(), N :: pos_integer(), [term()]) -> boolean().
'lists:keymember'(_, _, _) -> error(overlay).

%% the new element has to be a tuple
-spec 'lists:keystore'(Key :: term(), N :: pos_integer(), [T], New) -> [T | New, ...] when New :: tuple().
'lists:keystore'(_, _, _, _) -> error(overlay).

-spec 'lists:keydelete'(Key :: term(), N :: pos_integer(), [T]) -> [T].
'lists:keydelete'(_, _, _) -> error(overlay).

-spec 'lists:keytake'(Key :: term(), N :: pos_integer(), [T]) -> {value, T, [T]} | false.
'lists:keytake'(_, _, _) -> error(overlay).

%% OTP: number()
-spec 'lists:sum'([non_neg_integer()]) -> non_neg_integer();
                 ([integer()]) -> integer();
                 ([number()]) -> number().
'lists:sum'(_) -> error(overlay).

%% OTP: posix() | system_limit. The last clause hands every other term to erl_posix_msg:message/1, which
%% answers "unknown POSIX error: ..." for an atom it does not know.
-spec 'inet:format_error'(atom()) -> string().
'inet:format_error'(_) -> error(overlay).

%% OTP: undefined | {ok, Val} when Val :: term(), a result that fits every type
-spec 'application:get_env'(atom()) -> undefined | {ok, term()}.
'application:get_env'(_) -> error(overlay).

%% OTP: {error, Reason} when Reason :: term(). With that a case on the result that has a clause for one error only
%% (ranch:require/1) is reported for a clause that never matches, not for the errors it leaves out.
-spec 'application:start'(atom()) -> ok | {error, term()}.
'application:start'(_) -> error(overlay).
