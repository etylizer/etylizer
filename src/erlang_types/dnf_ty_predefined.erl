-module(dnf_ty_predefined).

-export([
  reorder/1,
  predefined/1,
  compare/2,
  empty/0,
  any/0,
  negate/1,
  intersect/2,
  union/2,
  difference/2,
  is_empty/2,
  normalize/3,
  unparse/2,
  all_variables/2
]).

-export_type([type/0]).

-define(ELEMENTS, 5).

-opaque type() :: <<_:?ELEMENTS>>.
-type set_of_constraint_sets() :: constraint_set:set_of_constraint_sets().
-type ast_ty() :: ast:ty().

% TODO benchmark how much faster the bit representation is (O(n) vs O(1))
% predefined(Predef) -> [Predef].
% empty() -> [].
% any() -> [ '[]', float, pid, port, reference ].
% is_empty([], ST) -> {true, ST};
% is_empty(_, ST) -> {false, ST}.
% negate(All) -> any() -- All.
% union(P1, P2) -> lists:usort(P1 ++ P2).
% intersect(P1, P2) -> [X || X <- P1, lists:member(X, P2)].
% diff(I1, I2) -> intersect(I1, negate(I2)).
 
reorder(X) -> X.

-spec compare(T, T) -> eq | lt | gt when T :: type().
compare(R1, R2) -> case R1 < R2 of true -> lt; _ -> case R1 > R2 of true -> gt; _ -> eq end end.

-spec predefined('[]' | float | pid | port | reference) -> type().
% Map each element to a unique bit position
predefined('[]') -> <<1:?ELEMENTS>>; 
predefined(float) -> <<2:?ELEMENTS>>;
predefined(pid) -> <<4:?ELEMENTS>>;
predefined(port) -> <<8:?ELEMENTS>>;
predefined(reference) -> <<16:?ELEMENTS>>.

-spec empty() -> type().
empty() -> <<0:?ELEMENTS>>.

% The full set (all bits set for ?ELEMENTS elements: 1+2+4+8+16 = 31)
-spec any() -> type().
any() -> <<31:?ELEMENTS>>.

-spec is_empty(type(), T) -> {boolean(), T}.
is_empty(<<0:?ELEMENTS>>, ST) -> {true, ST};
is_empty(_, ST) -> {false, ST}.

-spec negate(T) -> T when T :: type().
negate(<<N:?ELEMENTS>>) -> <<(31 bxor N):?ELEMENTS>>.

-spec union(T, T) -> T when T :: type().
union(<<P1:?ELEMENTS>>, <<P2:?ELEMENTS>>) -> <<(P1 bor P2):?ELEMENTS>>.

-spec intersect(T, T) -> T when T :: type().
intersect(<<P1:?ELEMENTS>>, <<P2:?ELEMENTS>>) -> <<(P1 band P2):?ELEMENTS>>.

-spec difference(T, T) -> T when T :: type().
difference(I1, I2) -> intersect(I1, negate(I2)).

-spec normalize(type(), _, ST) -> {set_of_constraint_sets(), ST}.
normalize(Dnf, _, ST) ->
  % Fig. 3 Line 3
  case is_empty(Dnf, #{}) of
    {true, _} -> {[[]], ST};
    {false, _} -> {[], ST}
  end.

-spec unparse(type(), T) -> {ast_ty(), T}.
unparse(<<Bitmask:?ELEMENTS>>, ST) ->
  {lists:foldl(
        fun({Atom, Bit}, Acc) ->
            case Bit band Bitmask of
                0 -> Acc;
                _ -> 
                [case Atom of 
                  '[]' -> {empty_list};
                  _ -> {predef, Atom}
                end | Acc]
            end
        end,
        [],
        [ {'[]', 1}, {float, 2}, {pid, 4}, {port, 8}, {reference, 16} ]
    ), ST}.

-spec all_variables(type(), _) -> sets:set().
all_variables(_, _) -> sets:new().
