-module(overlay_calendar).
-compile([export_all, nowarn_export_all]).

% Specs for the functions of calendar.erl that have none upstream.

-type option() :: {offset, calendar:offset()} | {time_designator, byte()}
                | {unit, calendar:rfc3339_time_unit()} | {return, string | binary}.
-type unit() :: second | millisecond | microsecond | nanosecond | native.

-spec 'calendar:system_time_to_rfc3339_do'(integer(), [option()], unit(), calendar:offset()) -> calendar:rfc3339_string().
'calendar:system_time_to_rfc3339_do'(_, _, _, _) -> error(overlay).
-spec 'calendar:check'(integer(), [option()], integer()) -> ok.
'calendar:check'(_, _, _) -> error(overlay).
-spec 'calendar:system_time_to_datetime'(integer()) -> calendar:datetime().
'calendar:system_time_to_datetime'(_) -> error(overlay).
-spec 'calendar:offset'(calendar:offset(), integer()) -> string().
'calendar:offset'(_, _) -> error(overlay).
-spec 'calendar:offset_adjustment'(integer(), unit(), calendar:offset()) -> integer().
'calendar:offset_adjustment'(_, _, _) -> error(overlay).
-spec 'calendar:offset_string_adjustment'(integer(), unit(), [byte()]) -> integer().
'calendar:offset_string_adjustment'(_, _, _) -> error(overlay).
-spec 'calendar:local_offset'(integer(), unit()) -> integer().
'calendar:local_offset'(_, _) -> error(overlay).
-spec 'calendar:mod'(integer(), pos_integer()) -> non_neg_integer().
'calendar:mod'(_, _) -> error(overlay).
-spec 'calendar:fraction_str'(pos_integer(), integer()) -> string().
'calendar:fraction_str'(_, _) -> error(overlay).
-spec 'calendar:factor'(unit()) -> pos_integer().
'calendar:factor'(_) -> error(overlay).
-spec 'calendar:log10'(1000 | 1000000 | 1000000000) -> 3 | 6 | 9.
'calendar:log10'(_) -> error(overlay).
-spec 'calendar:pad'(non_neg_integer(), string()) -> string().
'calendar:pad'(_, _) -> error(overlay).
-spec 'calendar:pad2'(non_neg_integer()) -> string().
'calendar:pad2'(_) -> error(overlay).
-spec 'calendar:pad4'(integer()) -> string().
'calendar:pad4'(_) -> error(overlay).
