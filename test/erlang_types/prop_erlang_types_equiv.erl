-module(prop_erlang_types_equiv).

-include_lib("proper/include/proper.hrl").
-include_lib("eunit/include/eunit.hrl").

-define(COMMON_ERLANG_ATOMS, [
    ok, error, undefined, true, false,
    reply, noreply, stop, ignore, timeout,
    normal, shutdown, kill, init, start,
    start_link, handle_call, handle_cast, handle_info, code_change,
    terminate, state, config, data, value, result,
    request, response, up, down, active, inactive,
    open, closed, connected, disconnected, ready,
    waiting, busy, idle, success, failure, enabled, disabled,
    on, off, yes, no, all, none, some, any, default,
    custom, local, remote, internal, external, primary, secondary,
    master, slave, leader, follower, supervisor, worker, gen_server,
    gen_statem, gen_event, gen_fsm, ets, dets, mnesia, pg,
    pg2, sys, proc_lib, application, module, function, export,
    priv, debug, info, warning, error_logger, critical, fatal,
    trace, log, test, prod, dev, staging
]).

-define(COMMON_INTEGER_RANGES, [
    {0, 255}, {-128, 127}, {0, 65535}, {-32768, 32767},
    {0, 4294967295}, {-2147483648, 2147483647}, {0, 65535},
    {0, 1023}, {1024, 49151}, {49152, 65535}, {200, 299},
    {400, 599}, {32, 126}, {0, 31}, {128, 255}, {0, 16#FFFF},
    {0, 16#10FFFF}, {-3, 3}, {0, 16#FFFFFFFF}, {0, 16#FFFFFFFF},
    {0, 16#FFFFFFFFFFFFFFFF}, {0, 1023}, {0, 16#FFFFFFFF}, {0, 255},
    {0, 65535}, {0, 100}, {0, 359}, {-90, 90}, {-180, 180},
    {0, '*'}, {'*', 0}, {'*', '*'}
]).

-define(COMMON_INTEGERS, [
    0, 1, 2, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096,
    8192, 65536, 1048576, 16777216, 4294967296, 80, 443,
    22, 25, 53, 3306, 5432, 27017, 6379, 9200, 200, 201,
    202, 204, 301, 302, 400, 401, 403, 404, 405, 500, 501,
    502, 503, 60, 3600, 86400, 604800, 31536000, 4096, 8192,
    16384, 65536, 16#FFFFFFFF, 16#FFFFFFFFFFFFFFFF
]).


tany() -> {predef, any}.
tempty() -> {predef, none}.
tnegation(A) -> {negation, A}.
tunion(A, B) -> {union, [A, B]}.
tintersection(A, B) -> {intersection, [A, B]}.
tarrow(A, B) -> {fun_full, [A], B}.
tproduct(A, B) -> {tuple, [A, B]}.
tlist(A) -> {list, A}.
tfun(As, B) -> {fun_full, As, B}.
tvar(Variables) ->
  ?LET(Varname, oneof(Variables), {named, 0, {ty_ref, '.', Varname, 0}, []}).
ttypevar() ->
  ?LET(Varname, oneof([alpha, beta, gamma, delta, epsilon]), {var, Varname}).
tpredef() ->
  ?LET(Predef, oneof([float, reference, pid, port]), {predef, Predef}).
tatom() ->
  ?LET(Atom, oneof(?COMMON_ERLANG_ATOMS), {singleton, Atom}).
tinteger_range() ->
  ?LET({Left, Right}, oneof(?COMMON_INTEGER_RANGES), {range, Left, Right}).
tinteger() ->
  ?LET(Int, oneof(?COMMON_INTEGERS), {range, Int, Int}).

limited_formula(Variables) ->
  ?SIZED(Size, limited_formula(Variables, Size, toplevel)).

tvar_if_not_toplevel(Variables, Mode) -> 
  case Mode of toplevel -> []; _ -> [{1, tvar(Variables)}] end.

-define(F, limited_formula(Variables, Size div 2, Mode)).
-define(Fi, limited_formula(Variables, Size div 2, inside)).

limited_formula(Variables, Size, Mode) when Size =< 1 ->
  frequency([
    {1, tempty()},
    {1, ttypevar()},
    {3, tatom()},
    {1, tinteger_range()},
    {1, tinteger()},
    {1, tpredef()},
    {1, {empty_list}},
    {1, tany()}
  ] ++ tvar_if_not_toplevel(Variables, Mode)
);
limited_formula(Variables, Size, Mode) ->
  frequency([
    {2, tempty()},
    {2, tany()},
    {1, ?LAZY(?LET(A, ?F, tnegation(A))) },
    {4, ?LAZY(?LET({A, B}, {?F, ?F}, tunion(A, B))) },
    {4, ?LAZY(?LET({A, B}, {?F, ?F}, tintersection(A, B))) },
    {8, ?LAZY(?LET({A, B}, {?Fi, ?Fi}, tproduct(A, B))) },
    {1, ?LAZY(?LET({A}, {?Fi}, tlist(A))) },
    {4, ?LAZY(?LET({A, B}, {?Fi, ?Fi}, tarrow(A, B))) },
    {1, ?LAZY(?LET({As, B}, {list(?Fi), ?Fi}, tfun(As, B))) }
  ] ++ tvar_if_not_toplevel(Variables, Mode)
).

system(Variables) ->
  ?SUCHTHAT(Ty, ?LET(Formulas, [limited_formula(Variables) || _ <- Variables], 
    maps:from_list(lists:zip(Variables, Formulas))
  ), valid_system(Ty)).

% property tests with fixed timeouts are not too stable, 
% but randomly generated test cases shouldn't take longer than these timeouts
% currently starts failing after with n > 10000
-define(PARSETIMEOUTMS, 500).
-define(EMPTYTIMEOUTMS, 50).

% property that checks if we can parse a random type and check emptyness 
% in a reasonable amount of time
prop_parse_and_emptiness() -> 
  ?FORALL(X, ?LET(Types, nonempty_list(atom()), system(Types)), begin 
    global_state:with_new_state(fun() ->
      maps:foreach(fun(VarName, AstTy) -> ty_parser:extend_symtab(VarName, {ty_scheme, [], AstTy}) end, X),

      maps:map(fun(Name, _) -> 
        Ty = {named, noloc, {ty_ref, '.', Name, 0}, []},
        T0 = os:system_time(millisecond),
        Parsed = ty_parser:parse(Ty),
        true = ((T1 = os:system_time(millisecond)) - T0) < ?PARSETIMEOUTMS,
        ty_node:is_empty(Parsed),
        true = (os:system_time(millisecond) - T1) < ?EMPTYTIMEOUTMS
      end, X),
      true
    end)
  end).

% in addition to prop_parse_and_emptiness, 
% this should ensure that the growing state in ty_parser 
% won't result in slow down of the whole parser
prop_parse_and_emptiness_cache() -> 
  ?SETUP(
    fun() ->
      global_state:clean(),
      global_state:init(),
      T00 = os:system_time(millisecond),
      fun() -> 
        T11 = os:system_time(millisecond),
        io:format(user,"~p ms (~p parsed types cached)~n", [T11-T00, length(ets:tab2list(ty_parser_cache))]),
        global_state:clean(),
        ok
      end
    end,
    ?FORALL(X, ?LET(Types, nonempty_list(atom()), system(Types)), begin 
      maps:foreach(fun(VarName, AstTy) -> ty_parser:extend_symtab({test_ref, '.', VarName, 0}, {ty_scheme, [], AstTy}) end, X),

      maps:map(fun(Name, _) -> 
        Ty = {named, noloc, {ty_ref, '.', Name, 0}, []},
        T0 = os:system_time(millisecond),
        Parsed = ty_parser:parse(Ty),
        true = ((T1 = os:system_time(millisecond)) - T0) < ?PARSETIMEOUTMS,
        ty_node:is_empty(Parsed),
        true = (os:system_time(millisecond) - T1) < ?EMPTYTIMEOUTMS
      end, X),
      true 
    end)
  ).

% generates subtype checks that look like S & !T
prop_subtype_instances() -> 
  ?FORALL(X, ?LET(Types, nonempty_list(atom()), system(Types)), begin 
    global_state:with_new_state(fun() ->
      maps:foreach(fun(VarName, AstTy) -> ty_parser:extend_symtab({test_ref, '.', VarName, 0}, {ty_scheme, [], AstTy}) end, X),

      AllTypes = [ty_parser:parse({named, noloc, {ty_ref, '.', Name, 0}, []}) || {Name, _} <- maps:to_list(X)],

      Instances = [ty_node:intersect(A, ty_node:negate(B)) || A <- AllTypes, B <- AllTypes],
      lists:foreach(fun(Ty) -> 
        T0 = os:system_time(millisecond),
        ty_node:is_empty(Ty),
        true = (os:system_time(millisecond) - T0) < 10 % if something is slower than 10ms -> good random test case
      end, Instances),
      true 
    end)
  end).

% T, parse T as T', unparse T' as T'', T and T'' should be equivalent
prop_parse_unparse_equivalency() -> 
  ?FORALL(X, ?LET(Types, nonempty_list(atom()), system(Types)), begin 
    global_state:with_new_state(fun() ->
      maps:foreach(fun(VarName, AstTy) -> ty_parser:extend_symtab({test_ref, '.', VarName, 0}, {ty_scheme, [], AstTy}) end, X),
      [begin 
         % io:format(user,"Parsing ~p...~n", [Name]),
         {Time1, T} = timer:tc(fun() -> ty_parser:parse({named, noloc, {ty_ref, '.', Name, 0}, []}) end),
         % io:format(user,"Unparsing ~p...~n~p~n", [T, ty_node:dump(T)]),
         {Time2, Tp} = timer:tc(fun() -> ty_parser:unparse(T) end),
         case Time2/Time1 > 100 of 
           true -> 
             io:format(user,"Unparse 100x slower than parse: ~p vs ~p~n", [Time1, Time2]),
             error(todo);
           _ -> ok
         end
          
       end
       || {Name, _} <- maps:to_list(X)],
      true 
    end)
  end).

% checks if for each variable the recursive system
% that variable is only contained under a type constructor (if at all)
valid_system(System) ->
  lists:all(fun valid_rec/1, maps:to_list(System)).
  
valid_rec({_, {empty_list}}) -> true;
valid_rec({_, {predef, _}}) -> true;
valid_rec({_, {var, _}}) -> true;
valid_rec({_, {singleton, _}}) -> true;
valid_rec({_, {range, _, _}}) -> true;
valid_rec({Ty, {negation, L}}) -> valid_rec({Ty, L});
valid_rec({Ty, {union, L}}) -> lists:all(fun(E) -> valid_rec({Ty, E}) end, L);
valid_rec({Ty, {intersection, L}}) -> lists:all(fun(E) -> valid_rec({Ty, E}) end, L);
valid_rec({_, {fun_full, _, _}}) -> true;
valid_rec({_, {list, _}}) -> true;
valid_rec({_, {tuple, _}}) -> true;
valid_rec({Ty, {named, _, {ty_ref, '.', Ty, 0}, []}}) -> false;
valid_rec({_, {named, _, _Ty, []}}) -> false. % lets say recursion happens only under a type constructor for any variable
  
