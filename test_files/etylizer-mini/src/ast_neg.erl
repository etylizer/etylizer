-module(ast_neg).

-export([mk_negation/1]).

-type ty() :: {ty()} | {foo}.

-spec mk_negation(ty()) -> ty().
mk_negation({_}) -> {foo}.
