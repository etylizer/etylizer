-module(subty).

-export([
  is_subty/3,
  is_equivalent/3,
  is_subty_bdd/4,

  simple_empty/2,
  is_empty/2,
  is_any/2
]).

is_equivalent(SymTab, S, T) -> is_subty(SymTab, S,T) andalso is_subty(SymTab, T,S).

-spec is_subty(symtab:t(), ast:ty(), ast:ty()) -> boolean().
is_subty(Symtab, T1, T2) ->
  H1 = erlang:phash2(T1),
  H2 = erlang:phash2(T2),

  memoize:memo_fun(
    {subty_memo, {H1, H2}},
    fun() ->
    S_internal = ty_rec:norm(T1),
    T_internal = ty_rec:norm(T2),
    is_subty_bdd(S_internal, T_internal, Symtab, sets:new())
                   end
  ).


is_any(T, Sym) ->
  is_subty(Sym, {predef, any}, T).

is_empty(T, Sym) ->
  is_subty(Sym, T, {predef, none}).


is_subty_bdd(T1, T2, Symtab, Memo) ->
  SnT = ty_rec:diff(T1, T2),
  ty_rec:is_empty(SnT, Symtab, Memo).




simple_empty({improper_list, A, B}, Sym) ->
  NewA = simple_empty(A, Sym),
  NewB = simple_empty(B, Sym),

  case ( is_empty(NewA, Sym) orelse is_empty(NewB, Sym)) of
    true ->
      {predef, none};
    _ -> {improper_list, NewA, NewB}
  end;
simple_empty({list, A}, Sym) ->
  NewA = simple_empty(A, Sym),
  case ( is_empty(NewA, Sym) ) of
    true ->
      {empty_list};
    _ -> {list, NewA}
  end;
simple_empty({tuple, C}, Sym) ->
  Simpl = lists:map(fun(E) -> simple_empty(E, Sym) end, C),
  case lists:any(fun(E) -> is_empty(E, Sym) end, Simpl) of
    true ->
      {predef, none};
    _ -> {tuple, Simpl}
  end;
simple_empty({fun_full, C, T}, Sym) ->
  {fun_full, lists:map(fun(Cs) -> simple_empty(Cs, Sym) end, C), simple_empty(T, Sym)};
simple_empty({negation, C}, Sym) ->
  St = simple_empty(C, Sym),
  case is_empty(St, Sym) of
    true -> {predef, any};
    _ ->
      case is_any(St, Sym) of
        true -> {predef, none};
        _ -> {negation, St}
      end
  end;
simple_empty({intersection, []}, _Sym) -> {predef, any};
simple_empty({intersection, C}, Sym) ->
  Simpl = lists:map(fun(E) -> simple_empty(E, Sym) end, C),
  NoAny = lists:usort(lists:filter(fun(E) -> not is_any(E, Sym) end, Simpl)),

  case lists:any(fun(E) -> is_empty(E, Sym) end, NoAny) of
    true ->
      {predef, none};
    _ -> case {is_empty({intersection, NoAny}, Sym), NoAny} of
           {true, _} -> {predef, none};
           {_, [X]} -> X;
           {_, []} -> {predef, any};
           _ -> move_covariance_inside({intersection, NoAny}, Sym)
         end
  end;
simple_empty({union, []}, _Sym) -> {predef, none};
simple_empty({union, C}, Sym) ->
  Simpl = lists:map(fun(E) -> simple_empty(E, Sym) end, C),
  NoNone = lists:usort(lists:filter(fun(E) -> not is_empty(E, Sym) end, Simpl)),

  case (lists:any(fun(E) -> is_any(E, Sym) end, NoNone)) of
    true ->
      {predef, any};
    _ -> case NoNone of [X] -> X; [] -> {predef, none}; _ -> merge_integers({union, NoNone}, Sym) end
  end;
simple_empty(T = {empty_list}, _Sym) -> T;
simple_empty(T = {var, _}, _Sym) -> T;
simple_empty(T = {predef, _}, _Sym) -> T;
simple_empty(T = {predef_alias, _}, _Sym) -> T;
simple_empty(T = {singleton, _}, _Sym) -> T;
simple_empty(T = {range, _, _}, _Sym) -> T;
simple_empty(T, _Sym) ->
  logger:error("Simple empty: ~p", [T]),
  throw(todo_p).

move_covariance_inside({intersection, Components}, Sym) ->
  {ImproperLists, Other} = lists:partition(fun({improper_list, _, _}) -> true; (_) -> false end, Components),

  case ImproperLists of
    [] -> move_tuple_inside({intersection, Components}, Sym);
    [_X] -> move_tuple_inside({intersection, Components}, Sym);
    _ ->
      New = {intersection,
          [{improper_list,
            {intersection, [A || {improper_list, A, _} <- ImproperLists]},
            {intersection, [B || {improper_list, _, B} <- ImproperLists]}
          }] ++ Other},
      New2 = simple_empty(New, Sym),
      New2
  end.

move_tuple_inside({intersection, Components}, Sym) ->
  {SingleTuples, Other} = lists:partition(fun({tuple, [_X]}) -> true; (_) -> false end, Components),

  case SingleTuples of
    []  -> move_2tuple_inside({intersection, Components}, Sym);
    [_X] -> move_2tuple_inside({intersection, Components}, Sym);
    _ ->
      New = {intersection,
          [{tuple,
            [{intersection, [X || {tuple, [X]} <- SingleTuples]}]
          }] ++ Other},
      New2 = simple_empty(New, Sym),
      New2
  end.

move_2tuple_inside({intersection, Components}, Sym) ->
  {Tupels2, Other} = lists:partition(fun({tuple, [_,_]}) -> true; (_) -> false end, Components),

  case Tupels2 of
    [] -> merge_integers({intersection, Components}, Sym);
    [_X] -> merge_integers({intersection, Components}, Sym);
    _ ->
      New = {intersection,
          [{tuple,
            [
              {intersection, [A || {tuple, [A, _]} <- Tupels2]},
              {intersection, [B || {tuple, [_, B]} <- Tupels2]}
            ]
          }] ++ Other},
      New2 = simple_empty(New, Sym),
      New2
  end.


merge_integers(Ty = {Op, Components}, _Sym) ->
  {RPInts, Other} = lists:partition(fun
                                      ({predef, integer}) -> true;
                                      ({range, _, _}) -> true;
                                      ({singleton, I}) when is_integer(I) -> true;
                                      (_) -> false
                                  end, Components),
  {RNInts, Other2} = lists:partition(fun
                                       ({negation, {predef, integer}}) -> true;
                                       ({negation, {range, _, _}}) -> true;
                                       ({negation, {singleton, I}}) when is_integer(I) -> true;
                                       (_) -> false
                                     end, Other),



  case RPInts ++ RNInts of
    [] -> Ty;
    [_] -> Ty;
    _ ->
      Conv = fun
               ({singleton, I}) -> rep_ints:interval(I, I);
               ({range, A, B}) -> rep_ints:interval(A, B);
               ({negation, {singleton, I}}) -> rep_ints:cointerval(I, I);
               ({predef, integer}) -> rep_ints:any();
               ({negation, {range, A, B}}) -> rep_ints:cointerval(A, B);
               ({negation, {predef, integer}}) -> rep_ints:empty()
             end,

      case Op of
        intersection ->
          PInts = case RPInts of [] -> [rep_ints:any()]; _ -> lists:map(Conv, RPInts) end,
          NInts = case RNInts of [] -> [rep_ints:any()]; _ -> lists:map(Conv, RNInts) end,
          Pp = lists:foldl(fun rep_ints:intersect/2, rep_ints:any(), PInts),
          Nn = lists:foldl(fun rep_ints:intersect/2, rep_ints:any(), NInts),
          I = rep_ints:intersect(Pp, Nn),
          EI = rep_ints:eval(I),

          case {intersection, [EI] ++ Other2} of
            {intersection, [X]} -> X;
            Z -> Z
          end;
        union ->
          PInts = case RPInts of [] -> [rep_ints:empty()]; _ -> lists:map(Conv, RPInts) end,
          NInts = case RNInts of [] -> [rep_ints:empty()]; _ -> lists:map(Conv, RNInts) end,
          Pp = lists:foldl(fun rep_ints:union/2, rep_ints:empty(), PInts),
          Nn = lists:foldl(fun rep_ints:union/2, rep_ints:empty(), NInts),
          I = rep_ints:union(Pp, Nn),
          EI = rep_ints:eval(I),

          case {union, [EI] ++ Other2} of
            {union, [X]} -> X;
            Z -> Z
          end
      end
  end.

