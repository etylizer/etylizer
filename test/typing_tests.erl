-module(typing_tests).

-include_lib("eunit/include/eunit.hrl").

-import(stdtypes, [tyscm/2, tatom/0, tint/0, tvar/1, tfun/2]).

is_more_general_test() ->
    AtomToAtom = tyscm([], tfun([tatom()], tatom())),
    AtomToInt = tyscm([], tfun([tatom()], tint())),
    AlphaToAlpha = tyscm([alpha], tfun([tvar(alpha)], tvar(alpha))),
    AlphaToBeta = tyscm([alpha, beta], tfun([tvar(alpha)], tvar(beta))),
    Tab = symtab:empty(),
    true = typing:more_general(AtomToAtom, AtomToAtom, Tab),
    true = typing:more_general(AtomToInt, AtomToInt, Tab),
    false = typing:more_general(AtomToAtom, AtomToInt, Tab),
    false = typing:more_general(AtomToAtom, AlphaToAlpha, Tab),
    false = typing:more_general(AtomToAtom, AlphaToBeta, Tab),
    true = typing:more_general(AlphaToAlpha, AtomToAtom, Tab),
    false = typing:more_general(AlphaToAlpha, AtomToInt, Tab),
    true = typing:more_general(AlphaToBeta, AtomToInt, Tab).
