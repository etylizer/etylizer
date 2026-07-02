-module(scoping).

-compile([export_all, nowarn_export_all, nowarn_unused_vars]).

-spec ff(f) -> ok.
ff(_) -> error(todo).

-spec gg(g) -> ok.
gg(_) -> error(todo).

-spec hh4(f | g1 | g2) -> ok.
hh4(_I) -> error(todo).

-spec hh(f | g) -> ok.
hh(_I) -> error(todo).

-spec gg2(g1 | g2) -> ok.
gg2(_I) -> error(todo).

-spec c_inline(a | b) -> ok.
c_inline(A1) ->
  case A1 of
    a -> ff(f) ;
    b -> gg(g)
  end,
  ok.


-spec c_bound2(a | b) -> ok.
c_bound2(A1) ->
  case A1 of
    a -> T = f, ff(T);
    b -> T = g, gg(T)
  end,
  ok.


-spec c_renamed(a | b) -> ok.
c_renamed(A1) ->
  case A1 of
    a -> T = f, ff(T);
    b -> T2 = g, gg(T2)
  end,
  ok.

-spec c_after(a | b) -> ok.
c_after(A1) ->
  case A1 of
    a -> T = f;
    b -> T = g
  end,
  hh(T).

-spec c_same(a | b) -> ok.
c_same(A1) ->
  case A1 of
    a -> T = f, ff(T);
    b -> T = f, ff(T)
  end,
  ok.

-spec c_one_use(a | b) -> ok.
c_one_use(A1) ->
  case A1 of
    a -> T = f, ff(T);
    b -> T = g, ok
  end,
  ok.

-spec c_nested(a | b, c | d) -> ok.
c_nested(A1, A2) ->
  case A1 of
    a -> T = f, ff(T);
    b ->
      case A2 of
        c -> T = g1;
        d -> T = g2
      end,
      gg2(T)
  end,
  ok.


-spec c_nested_after(a | b, c | d) -> ok.
c_nested_after(A1, A2) ->
  case A1 of
    a ->
          T = f;
    b ->
          case A2 of
            c -> T = g1;
            d -> T = g2
          end
  end,
  hh4(T).


-spec c_pat_after({ok, f} | {err, g}) -> ok.
c_pat_after(A1) ->
  case A1 of
    {ok, T} -> ok;
    {err, T} -> ok
  end,
  hh(T).

-spec c_wrong_fail(a | b) -> ok.
c_wrong_fail(A1) ->
  case A1 of
    a ->
          T = f,
          gg(T);
    b ->
          T = g,
          gg(T)
  end,
  ok.

-spec c_wrong_after_fail(a | b) -> ok.
c_wrong_after_fail(A1) ->
  case A1 of
    a ->
          T = f;
    b ->
          T = g
  end,
  ff(T).
