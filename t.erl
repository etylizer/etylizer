-module(t).

-compile([export_all, nowarn_export_all]).

-type ordset(T) :: [T].

-spec intersection(OrdsetList) -> Ordset when
      OrdsetList :: [ordset(_),...],
      Ordset :: ordset(_).
intersection([S1,S2|Ss]) -> intersection1(intersection(S1, S2), Ss);
intersection([S]) -> S.
%intersection(_) -> error(bad_state).

-spec intersection(Ordset1, Ordset2) -> Ordset3 when
      Ordset1 :: ordset(_),
      Ordset2 :: ordset(_),
      Ordset3 :: ordset(_).
intersection([E1|Es1], [E2|_]=Set2) when E1 < E2 -> intersection(Es1, Set2);
intersection([E1|_]=Set1, [E2|Es2]) when E1 > E2 -> intersection(Es2, Set1);
intersection([E1|Es1], [_E2|Es2]) -> [E1|intersection(Es1, Es2)];
intersection([], _) -> [];
intersection(_, []) -> [].


-spec intersection1(ordset(_), [ordset(_)]) -> ordset(_).
intersection1(S1, [S2|Ss]) -> intersection1(intersection(S1, S2), Ss);
intersection1(S1, []) -> S1.
