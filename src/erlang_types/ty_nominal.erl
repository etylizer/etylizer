-module(ty_nominal).

%% Atom type for nominal BDD nodes.
%% A nominal key identifies a nominal type by its module, name, and arity.

-export([
  equal/2,
  compare/2,
  leq/2,
  unparse/2,
  new/1,
  key/1
]).

-export_type([type/0, nominal_key/0]).

-type nominal_key() :: {atom(), atom(), non_neg_integer()}.
-opaque type() :: {nominal_tag, nominal_key()}.

-spec new(nominal_key()) -> type().
new(Key) -> {nominal_tag, Key}.

-spec key(type()) -> nominal_key().
key({nominal_tag, Key}) -> Key.

-spec equal(type(), type()) -> boolean().
equal(T1, T2) -> compare(T1, T2) =:= eq.

-spec compare(type(), type()) -> lt | eq | gt.
compare({nominal_tag, K1}, {nominal_tag, K2}) ->
  if K1 < K2 -> lt; K1 > K2 -> gt; true -> eq end.

-spec leq(type(), type()) -> boolean().
leq(T1, T2) ->
  C = compare(T1, T2),
  C =:= eq orelse C =:= lt.

-spec unparse(type(), ST) -> {ast:ty(), ST}.
unparse({nominal_tag, {Mod, Name, Arity}}, C) ->
  {{named, ast:loc_auto(), {ty_ref, Mod, Name, Arity}, []}, C}.
