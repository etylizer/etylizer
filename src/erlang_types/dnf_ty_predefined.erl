-module(dnf_ty_predefined).

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
 
compare(R1, R2) -> case R1 < R2 of true -> lt; _ -> case R1 > R2 of true -> gt; _ -> eq end end.

-define(ELEMENTS, 5).
% Map each element to a unique bit position
predefined('[]') -> <<1:?ELEMENTS>>; 
predefined(float) -> <<2:?ELEMENTS>>;
predefined(pid) -> <<4:?ELEMENTS>>;
predefined(port) -> <<8:?ELEMENTS>>;
predefined(reference) -> <<16:?ELEMENTS>>.

% The empty set (no bits set)
empty() -> <<0:?ELEMENTS>>.

% The full set (all bits set for ?ELEMENTS elements: 1+2+4+8+16 = 31)
any() -> <<31:?ELEMENTS>>.

% Check if the set is empty (bitmask is 0)
is_empty(<<0:?ELEMENTS>>, ST) -> {true, ST};
is_empty(_, ST) -> {false, ST}.

negate(<<N:?ELEMENTS>>) -> <<(31 bxor N):?ELEMENTS>>.

union(<<P1:?ELEMENTS>>, <<P2:?ELEMENTS>>) -> <<(P1 bor P2):?ELEMENTS>>.

intersect(<<P1:?ELEMENTS>>, <<P2:?ELEMENTS>>) -> <<(P1 band P2):?ELEMENTS>>.

difference(I1, I2) -> intersect(I1, negate(I2)).

normalize(Dnf, _Fixed, ST) ->
  % Fig. 3 Line 3
  case is_empty(Dnf, #{}) of
    {true, _} -> {[[]], ST};
    {false, _} -> {[], ST}
  end.

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

all_variables(_, _) -> sets:new().
