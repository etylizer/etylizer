-module(filtermap).
-compile(export_all).

-include_lib("eunit/include/eunit.hrl").

-spec my_filtermap(fun((T) -> boolean()), [T]) -> [T]
                ; (fun((T) -> {true, U} | false), [T]) -> [U]
                ; (fun((T) -> {true, U} | boolean()), [T]) -> [T | U].
% my_filtermap(F, L) ->
%     case L of
%         [] -> [];
%         [X|XS] -> 
%             case F(X) of
%                 false -> my_filtermap(F, XS);
%                 true -> [X | my_filtermap(F, XS)];
%                 {true, Y} -> [Y | my_filtermap(F, XS)]
%             end
%     end.


my_filtermap(_F, []) -> [];
my_filtermap(F, [X|XS]) ->
    case F(X) of
        false -> my_filtermap(F, XS);
        true -> [X | my_filtermap(F, XS)];
        {true, Y} -> [Y | my_filtermap(F, XS)]
    end.

-spec zf(fun((T) -> boolean() | {'true', X}), [T]) -> [(T | X)].
zf(F, L) ->
    my_filtermap(F, L).

-spec filtermap_app() -> ok.
filtermap_app() ->
    L = my_filtermap(fun (X) -> X == 0 end, [1,2,3,4]),
    case L of
      [] -> ok;
      _ -> error(bad_app)
    end,
    % [4, 8] = my_filtermap(fun (X) ->
    %     if X rem 2 == 0 -> {true, X*2};
    %        true -> false
    %     end end, [1,2,3,4]),
    ok.

-type dnf() :: {dnf, tuples}.
-spec dnf_intersect(dnf(), dnf()) -> dnf().
dnf_intersect(_,_) -> error(overlay).


-spec intersect({dnf(), #{integer() => dnf()}}, {dnf(), #{integer() => dnf()}}) -> {dnf(), #{integer() => dnf()}}.
intersect({DefaultT1, T1}, {DefaultT2, T2}) ->
  % get all keys
  AllKeys = maps:keys(T1) ++ maps:keys(T2),
  IntersectKey = fun(Key) ->
    dnf_intersect( maps:get(Key, T1, Key), maps:get(Key, T2, DefaultT2))
                 end,
  L = lists:map(fun(Key) -> {Key, IntersectKey(Key)} end, AllKeys),
  {
    dnf_intersect(DefaultT1, DefaultT2), 
    maps:from_list(L)
  }.


-type config() :: ok.
-type reason() :: ok.
-type read_result() :: {ok, config()} | {error, reason()} | {retry, pos_integer()}.

-spec read_config() -> read_result().
read_config() -> error(todo).
  
-spec f() -> ok.
f() ->
  % Later, in code:
  case read_config() of
      {ok, Config} -> ok;
      {error, Reason} -> error(Reason)
  end,
  ok.


% -doc "Returns a flattened version of `DeepList`.".
% -type deepList(A) :: [A | deepList(A)].
% -spec flatten(deepList(A), [A]) -> [A].
% flatten(L, Tail) ->
%   case L of
%     [H | T] when is_list(H) -> flatten(H, flatten(T, Tail));
%     [H | T] -> [H | flatten(T, Tail)];
%     [] -> Tail
%   end.

-type deepList(A) :: [A | deepList(A)].
-spec do_flatten(deepList(A), [A]) -> [A].
do_flatten(L, _Tail) ->
  case L of
    [H | _T] when is_list(H) ->
      do_flatten(H, []);
    _ -> error(todo)
  end. 


-type year()     :: non_neg_integer().
-type year1970() :: 1970..10000.	% should probably be 1970..
-type month()    :: 1..12.
-type day()      :: 1..31.
-type hour()     :: 0..23.
-type minute()   :: 0..59.
-type second()   :: 0..59.
-type daynum()   :: 1..7.
-type ldom()     :: 28 | 29 | 30 | 31. % last day of month
-type weeknum()  :: 1..53.

-type date()           :: {year(),month(),day()}.
-type time()           :: {hour(),minute(),second()}.
-type datetime()       :: {date(),time()}.
-type datetime1970()   :: {{year1970(),month(),day()},time()}.
-type yearweeknum()    :: {year(),weeknum()}.
-type day_of_year() :: 0..365.

-spec is_leap_year(Year) -> boolean() when
      Year :: year().
is_leap_year(Y) ->
    is_leap_year1(Y).

% OK
-spec is_leap_year1(year()) -> boolean().
is_leap_year1(Year) when Year rem 4 =:= 0, Year rem 100 > 0 ->
    true;
is_leap_year1(Year) when Year rem 400 =:= 0 ->
    true;
is_leap_year1(_) -> false.



% timeout
-spec year_day_to_date2(0 | 1, day_of_year()) -> {month(), 0..30}.
year_day_to_date2(_, Day) when Day < 31 ->
    {1, Day}; 
year_day_to_date2(E, Day) when 31 =< Day, Day < 59 + E ->
    {2, Day - 31}; 
year_day_to_date2(E, Day) when 59 + E =< Day, Day < 90 + E -> 
    {3, Day - (59 + E)}; 
year_day_to_date2(E, Day) when 90 + E =< Day, Day < 120 + E -> 
    {4, Day - (90 + E)};
year_day_to_date2(E, Day) when 120 + E =< Day, Day < 151 + E -> 
    {5, Day - (120 + E)}; 
year_day_to_date2(E, Day) when 151 + E =< Day, Day < 181 + E ->
    {6, Day - (151 + E)};
year_day_to_date2(E, Day) when 181 + E =< Day, Day < 212 + E -> 
    {7, Day - (181 + E)}; 
year_day_to_date2(E, Day) when 212 + E =< Day, Day < 243 + E ->
    {8, Day - (212 + E)};
year_day_to_date2(E, Day) when 243 + E =< Day, Day < 273 + E ->
    {9, Day - (243 + E)};
year_day_to_date2(E, Day) when 273 + E =< Day, Day < 304 + E ->
    {10, Day - (273 + E)};
year_day_to_date2(E, Day) when 304 + E =< Day, Day < 334 + E ->
    {11, Day - (304 + E)};
year_day_to_date2(E, Day) when 334 + E =< Day -> 
    {12, Day - (334 + E)}.


% crashes
-spec dm(month()) ->
	     0 | 31 | 59 | 90 | 120 | 151 | 181 | 212 | 243 | 273 | 304 | 334.
dm(1) -> 0;    dm(2) ->  31;   dm(3) ->   59;   dm(4) ->  90;
dm(5) -> 120;  dm(6) ->  151;  dm(7) ->  181;   dm(8) -> 212;
dm(9) -> 243;  dm(10) -> 273;  dm(11) -> 304;  dm(12) -> 334.

% fails type check
%  -spec last_day_of_the_month1
%     (non_neg_integer(), 2) -> 28 | 29
%   ; (non_neg_integer(), 4 | 6 | 9 | 11) -> 30
%   ; (non_neg_integer(), 1 | 3 | 5 | 7 | 8 | 10 | 12) -> 31.
% -spec last_day_of_the_month1(year(),month()) -> ldom().
% last_day_of_the_month1(_, 4) -> 30;
% last_day_of_the_month1(_, 6) -> 30;
% last_day_of_the_month1(_, 9) -> 30;
% last_day_of_the_month1(_,11) -> 30;
% last_day_of_the_month1(Y, 2) ->
%    case is_leap_year(Y) of
%       true -> 29;
%       _    -> 28
%    end;
% last_day_of_the_month1(_, M) when is_integer(M), M > 0, M < 13 ->
%     31.


%  -spec last_day_of_the_month1
%     (non_neg_integer(), 2) -> 28 | 29
%   ; (non_neg_integer(), 4 | 6 | 9 | 11) -> 30
%   ; (non_neg_integer(), 1 | 3 | 5 | 7 | 8 | 10 | 12) -> 31.
% last_day_of_the_month1(Y, M) ->
%   case M of 
%     Z when Z == 4; Z == 6; Z==9; Z==11 -> 30; % ; is logical OR
%     Z when Z == 2 ->
%       case is_leap_year(Y) of
%         true -> 29;
%         false -> 28
%       end;
%     _ -> 31
%   end.


% WORKS
 -spec last_day_of_the_month1
    (non_neg_integer(), 2) -> 28 | 29
  ; (non_neg_integer(), 4 | 6 | 9 | 11) -> 30
  ; (non_neg_integer(), 1 | 3 | 5 | 7 | 8 | 10 | 12) -> 31.
last_day_of_the_month1(Y, M) ->
  case M of 
    4 -> 30; 
    6 -> 30;
    9 -> 30;
    11 -> 30;
    2 ->
      case is_leap_year(Y) of
        true -> 29;
        false -> 28
      end;
    _ -> 31
  end.

% WORKS, SLOW 1500s
%  -spec last_day_of_the_month1
%     (non_neg_integer(), 2) -> 28 | 29
%   ; (non_neg_integer(), 4 | 6 | 9 | 11) -> 30
%   ; (non_neg_integer(), 1 | 3 | 5 | 7 | 8 | 10 | 12) -> 31.
% last_day_of_the_month1(_, 4) -> 30;
% last_day_of_the_month1(_, 6) -> 30;
% last_day_of_the_month1(_, 9) -> 30;
% last_day_of_the_month1(_, 11) -> 30;
% last_day_of_the_month1(Y, 2) ->
%   case is_leap_year(Y) of
%     true -> 29;
%     false -> 28
%   end;
% last_day_of_the_month1(_, _M) ->
%     31.
% 
% 
% Another way of transformation, type error! Bounds incorrect?
%  -spec last_day_of_the_month1
%     (non_neg_integer(), 2) -> 28 | 29
%   ; (non_neg_integer(), 4 | 6 | 9 | 11) -> 30
%   ; (non_neg_integer(), 1 | 3 | 5 | 7 | 8 | 10 | 12) -> 31.
% last_day_of_the_month1(Y0, M0) -> 
%   case {Y0, M0} of
%     {_, 4} -> 30;
%     {Y1, M1} -> 
%       case {Y1, M1} of
%         {_, 6} -> 30;
%         {Y2, M2} -> 
%           case {Y2, M2} of
%             {_, 9} -> 30;
%             {Y3, M3} -> 
%               case {Y3, M3} of
%                 {_, 11} -> 30;
%                 {Y4, M4} ->
%                   case {Y4, M4} of
%                     {Y0, 2} -> 
%                       case is_leap_year(Y0) of
%                         true -> 29;
%                         false -> 28
%                       end;
%                     {_, _M} -> 31
%                   end
%                 end
%               end
%             end
%   end.
 
% much faster, instantly!
% mechanic optimization, ignore _ parameters if encountered
%  -spec last_day_of_the_month1
%     (non_neg_integer(), 2) -> 28 | 29
%   ; (non_neg_integer(), 4 | 6 | 9 | 11) -> 30
%   ; (non_neg_integer(), 1 | 3 | 5 | 7 | 8 | 10 | 12) -> 31.
% last_day_of_the_month1(Y, M0) -> 
%   case M0 of
%     4 -> 30;
%     M1 -> 
%       case M1 of
%         6 -> 30;
%         M2 -> 
%           case M2 of
%             9 -> 30;
%             M3 -> 
%               case M3 of
%                 11 -> 30;
%                 M4 ->
%                   case {Y, M4} of
%                     {Y0, 2} -> 
%                       case is_leap_year(Y0) of
%                         true -> 29;
%                         false -> 28
%                       end;
%                     {_, _M} -> 31
%                   end
%                 end
%               end
%             end
%   end.