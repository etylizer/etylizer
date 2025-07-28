-module(ast_neg).

% We do not have an explicit type for records. We encode them as tuples instead.
-type ty() :: ty_some_list()| ty_predef().
-type ty_empty_list() :: {empty_list}.
-type ty_list() :: {list, ty()}.
-type ty_nonempty_list() :: {nonempty_list, ty()}.
-type ty_improper_list() :: {improper_list, ty(), ty()}.
-type ty_nonempty_improper_list() :: {nonempty_improper_list, ty(), ty()}.
-type ty_some_list() :: ty_empty_list() | ty_list() | ty_nonempty_list() | ty_improper_list()
                      | ty_nonempty_improper_list().
-type predef_name() :: any | none | pid | port | reference | float | integer | atom.
-type ty_predef() :: {predef, predef_name()}.

-export([
    mk_negation/1
]).

-spec mk_negation(ty()) -> ty().
mk_negation({predef, any}) -> {predef, none};
mk_negation(T) -> {negation, T}.
