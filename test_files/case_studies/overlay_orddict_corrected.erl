-module(overlay_orddict_corrected).
-compile([export_all, nowarn_export_all]).

% Corrected specs of orddict.erl: calls use them, the functions are checked against
% these and their specs upstream.

-spec 'orddict:append'(Key, Value, orddict:orddict(Key, [Value])) -> orddict:orddict(Key, [Value]).
'orddict:append'(_, _, _) -> error(overlay).
-spec 'orddict:append_list'(Key, [Value], orddict:orddict(Key, [Value])) -> orddict:orddict(Key, [Value]).
'orddict:append_list'(_, _, _) -> error(overlay).
-spec 'orddict:update_counter'(Key, pos_integer(), orddict:orddict(Key, pos_integer())) -> orddict:orddict(Key, pos_integer());
                              (Key, non_neg_integer(), orddict:orddict(Key, non_neg_integer())) -> orddict:orddict(Key, non_neg_integer());
                              (Key, integer(), orddict:orddict(Key, integer())) -> orddict:orddict(Key, integer());
                              (Key, float(), orddict:orddict(Key, float())) -> orddict:orddict(Key, float());
                              (Key, number(), orddict:orddict(Key, number())) -> orddict:orddict(Key, number()).
'orddict:update_counter'(_, _, _) -> error(overlay).
-spec 'orddict:merge'(fun((Key, Value1, Value2) -> Value), orddict:orddict(Key, Value1), orddict:orddict(Key, Value2)) ->
          orddict:orddict(Key, Value | Value1 | Value2).
'orddict:merge'(_, _, _) -> error(overlay).
