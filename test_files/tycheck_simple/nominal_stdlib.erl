-module(nominal_stdlib).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.
%
% This file contains minified nominal type patterns from the OTP stdlib,
% testing that our nominal checker handles real-world nominal types correctly.

%%%%%%%%%%%%%%%%%%%%%%%% TYPE DEFINITIONS %%%%%%%%%%%%%%%%%%%%%%%

% erl_anno (stdlib-7.2.1/src/erl_anno.erl:124-125)
-type column() :: pos_integer().
-nominal line() :: non_neg_integer().
-nominal location() :: line() | {line(), column()}.

% timer (stdlib-7.2.1/src/timer.erl:179)
-nominal time() :: non_neg_integer().

% code (kernel-10.5/src/code.erl:428-435)
-nominal debug_line() :: pos_integer().
-nominal debug_frame() :: non_neg_integer() | 'entry' | 'none'.
-nominal debug_name() :: binary() | 1..255.
-nominal debug_source() :: {'x', non_neg_integer()} | {'y', non_neg_integer()} | {value, any()}.
-nominal debug_value() :: {debug_name(), debug_source()}.
% -nominal debug_info() :: [{debug_line(), {debug_frame(), [debug_value()]}}].

% dialyzer (dialyzer-5.4/src/erl_types.erl:311) - simplified
-nominal erl_type() :: atom() | tuple().

% ssl (ssl-11.5.1/src/ssl.erl:1541) - simplified
% -nominal session_ticket() :: #{sni := binary()}.

%%%%%%%%%%%%%%%%%%%%%%%% erl_anno - LINE/LOCATION HIERARCHY %%%%%%%%%%%%%%%%%%%%%%%

-spec anno_line(location()) -> line().
anno_line({Line, _Column}) -> Line;
anno_line(Line) -> Line.

-spec anno_location_line(line()) -> location().
anno_location_line(Line) -> Line.

-spec anno_location_pair(line(), column()) -> location().
anno_location_pair(Line, Column) -> {Line, Column}.

-spec anno_new(location()) -> location().
anno_new(Loc) -> Loc.

-spec anno_set_line(line(), location()) -> location().
anno_set_line(Line, {_OldLine, Column}) -> {Line, Column};
anno_set_line(Line, _OldLine) -> Line.

%%%%%%%%%%%%%%%%%%%%%%%% erl_scan - CROSS-MODULE USAGE %%%%%%%%%%%%%%%%%%%%%%%

-spec scan_line({atom(), location(), any()}) -> line().
scan_line({_Tag, Anno, _Value}) -> anno_line(Anno).

-spec scan_location({atom(), location(), any()}) -> location().
scan_location({_Tag, Anno, _Value}) -> Anno.

%%%%%%%%%%%%%%%%%%%%%%%% timer - TIME ARITHMETIC %%%%%%%%%%%%%%%%%%%%%%%

-spec seconds(non_neg_integer()) -> time().
seconds(Seconds) -> 1000 * Seconds.

-spec minutes(non_neg_integer()) -> time().
minutes(Minutes) -> 1000 * 60 * Minutes.

-spec hours(non_neg_integer()) -> time().
hours(Hours) -> 1000 * 60 * 60 * Hours.

-spec hms(non_neg_integer(), non_neg_integer(), non_neg_integer()) -> time().
hms(H, M, S) -> hours(H) + minutes(M) + seconds(S).

-spec timer_sleep(time() | infinity) -> ok.
timer_sleep(T) when is_integer(T) -> ok;
timer_sleep(infinity) -> ok.

-spec timer_send_after(time(), any()) -> {ok, reference()}.
timer_send_after(Time, _Message) when is_integer(Time) -> {ok, make_ref()}.

%%%%%%%%%%%%%%%%%%%%%%%% code - COMPOUND/NESTED NOMINALS %%%%%%%%%%%%%%%%%%%%%%%

-spec make_debug_value(debug_name(), debug_source()) -> debug_value().
make_debug_value(Name, Source) -> {Name, Source}.

-spec make_debug_source_x(non_neg_integer()) -> debug_source().
make_debug_source_x(Reg) -> {x, Reg}.

-spec make_debug_source_y(non_neg_integer()) -> debug_source().
make_debug_source_y(Reg) -> {y, Reg}.

-spec make_debug_entry() -> debug_frame().
make_debug_entry() -> entry.

-spec make_debug_frame(non_neg_integer()) -> debug_frame().
make_debug_frame(N) -> N.

-spec make_debug_info_entry(debug_line(), debug_frame(), [debug_value()]) -> {debug_line(), {debug_frame(), [debug_value()]}}.
make_debug_info_entry(Line, Frame, Values) -> {Line, {Frame, Values}}.

%%%%%%%%%%%%%%%%%%%%%%%% erl_types - BROAD NOMINAL %%%%%%%%%%%%%%%%%%%%%%%

-spec t_any() -> erl_type().
t_any() -> any.

-spec t_none() -> erl_type().
t_none() -> none.

-spec t_is_any(erl_type()) -> boolean().
t_is_any(any) -> true;
t_is_any(_) -> false.

-spec t_is_none(erl_type()) -> boolean().
t_is_none(none) -> true;
t_is_none(_) -> false.

-spec t_atom() -> erl_type().
t_atom() -> {atom, any}.

-spec t_atom_val(atom()) -> erl_type().
t_atom_val(A) -> {atom, A}.

%%%%%%%%%%%%%%%%%%%%%%%% ssl - NOMINAL MAP TYPE %%%%%%%%%%%%%%%%%%%%%%%

% := not yet supported
% -spec make_session_ticket(binary()) -> session_ticket().
% make_session_ticket(Sni) -> #{sni => Sni}.
%
% -spec get_tickets({use_ticket, [session_ticket()]}) -> [session_ticket()].
% get_tickets({use_ticket, Tickets}) -> Tickets.
