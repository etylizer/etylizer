-module(filtermap).
-compile([export_all, nowarn_export_all]).

-include_lib("eunit/include/eunit.hrl").

 -spec last_day_of_the_month1
    (non_neg_integer(), 2) -> 28
  ; (non_neg_integer(), 4 | 6 | 9 | 11) -> 30
  ; (non_neg_integer(), 1 | 3 | 5 | 7 | 8 | 10 | 12) -> 31.
last_day_of_the_month1(_, 4) -> 30;
last_day_of_the_month1(_, 6) -> 30;
last_day_of_the_month1(_, 9) -> 30;
last_day_of_the_month1(_, 11) -> 30;
last_day_of_the_month1(Y, 2) -> 28;
last_day_of_the_month1(_, _) ->
    31.

 -spec last_day_of_the_month2
    (non_neg_integer(), 2) -> 28
  ; (non_neg_integer(), 4 | 6 | 9 | 11) -> 30
  ; (non_neg_integer(), 1 | 3 | 5 | 7 | 8 | 10 | 12) -> 31.
last_day_of_the_month2(X0, X1) -> 
  case {X0, X1} of
    {_, 4} -> 30;
    {_, 6} -> 30;
    {_, 9} -> 30;
    {_, 11} -> 30;
    {Y, 2} -> 28;
    {_, _} -> 31
  end.

 -spec last_day_of_the_month3
    (non_neg_integer(), 2) -> 28
  ; (non_neg_integer(), 4 | 6 | 9 | 11) -> 30
  ; (non_neg_integer(), 1 | 3 | 5 | 7 | 8 | 10 | 12) -> 31.
last_day_of_the_month3(A1, A2) -> 
  case A2 of
    4 -> 30;
    _ ->
    case A2 of
      6 -> 30;
      _ ->
      case A2 of
        9 -> 30;
        _ ->
        case A2 of
          11 -> 30;
          _ ->
          case {A1, A2} of
            {Y, 2} -> 28;
            _ ->
              case A2 of
                _M -> 31
              end
          end
        end 
      end
    end
  end.
