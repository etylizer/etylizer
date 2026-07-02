-module(typing_tests).

-include_lib("eunit/include/eunit.hrl").

-import(stdtypes, [tyscm/2, tatom/0, tint/0, tvar/1, tfun/2]).

is_more_general_test() ->
    global_state:with_new_state(fun() ->
        AtomToAtom = tyscm([], tfun([tatom()], tatom())),
        AtomToInt = tyscm([], tfun([tatom()], tint())),
        AlphaToAlpha = tyscm([alpha], tfun([tvar(alpha)], tvar(alpha))),
        AlphaToBeta = tyscm([alpha, beta], tfun([tvar(alpha)], tvar(beta))),
        Tab = symtab:empty(),
        L = ast:loc_auto(),
        true = typing_infer:more_general(L, AtomToAtom, AtomToAtom, Tab),
        true = typing_infer:more_general(L, AtomToInt, AtomToInt, Tab),
        false = typing_infer:more_general(L, AtomToAtom, AtomToInt, Tab),
        false = typing_infer:more_general(L, AtomToAtom, AlphaToAlpha, Tab),
        false = typing_infer:more_general(L, AtomToAtom, AlphaToBeta, Tab),
        true = typing_infer:more_general(L, AlphaToAlpha, AtomToAtom, Tab),
        false = typing_infer:more_general(L, AlphaToAlpha, AtomToInt, Tab),
        true = typing_infer:more_general(L, AlphaToBeta, AtomToInt, Tab)
    end).
