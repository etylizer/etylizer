-module(filtermap).
-compile([export_all, nowarn_export_all]).

-include_lib("eunit/include/eunit.hrl").

% WORKS, SLOW 1500s
 -spec last_day_of_the_month1
    (non_neg_integer(), 2) -> 28 | 29
  ; (non_neg_integer(), 4 | 6 | 9 | 11) -> 30
  ; (non_neg_integer(), 1 | 3 | 5 | 7 | 8 | 10 | 12) -> 31.
last_day_of_the_month1(_, 4) -> 30;
last_day_of_the_month1(_, 6) -> 30;
last_day_of_the_month1(_, 9) -> 30;
last_day_of_the_month1(_, 11) -> 30;
last_day_of_the_month1(Y, 2) ->
  case is_leap_year(Y) of
    true -> 29;
    false -> 28
  end;
last_day_of_the_month1(_, _M) ->
    31.

% -spec last_day_of_the_month1
%     (non_neg_integer(), 2) -> 28 | 29
%   ; (non_neg_integer(), 4 | 6 | 9 | 11) -> 30
%   ; (non_neg_integer(), 1 | 3 | 5 | 7 | 8 | 10 | 12) -> 31.
% last_day_of_the_month1(A, B) ->
%   case {A, B} of
%     {_, 4} -> 30;
%     {_, 6} -> 30;
%     {_, 9} -> 30;
%     {_, 11} -> 30;
%     {Y, 2} -> 
%       case is_leap_year(Y) of
%         true -> 29;
%         false -> 28
%       end;
%     {_, _M} -> 31
%   end.

 -spec last_day_of_the_month2 (non_neg_integer(), 1 | 2 | 3) -> integer().
last_day_of_the_month2(_, 1) -> 30; 
last_day_of_the_month2(_, 3) -> 20; 
last_day_of_the_month2(Y, 2) ->
  case is_leap_year(Y) of
    true -> 29;
    false -> 28
  end.
 
% much faster, instantly!
% mechanic optimization, ignore _ parameters if encountered
 -spec last_day_of_the_month1
    (non_neg_integer(), 2) -> 28 | 29
  ; (non_neg_integer(), 4 | 6 | 9 | 11) -> 30
  ; (non_neg_integer(), 1 | 3 | 5 | 7 | 8 | 10 | 12) -> 31.
last_day_of_the_month1(Y, M0) -> 
  case M0 of
    4 -> 30;
    M1 -> 
      case M1 of
        6 -> 30;
        M2 -> 
          case M2 of
            9 -> 30;
            M3 -> 
              case M3 of
                11 -> 30;
                M4 ->
                  case {Y, M4} of
                    {Y0, 2} -> 
                      case is_leap_year(Y0) of
                        true -> 29;
                        false -> 28
                      end;
                    {_, _M} -> 31
                  end
                end
              end
            end
end.

-type year()     :: non_neg_integer().


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
%   end.