-module(dnf_ty_bitstring).

% Bitstring type representation using a 3-bit field.
% The universe of all bitstrings is partitioned into three disjoint categories:
%   Bit 0 (value 1): empty bitstring <<>> (size = 0)
%   Bit 1 (value 2): non-empty byte-aligned (size > 0, size mod 8 = 0)
%   Bit 2 (value 4): non-empty non-byte-aligned (size > 0, size mod 8 /= 0)
%
% Common types:
%   bitstring()          = 7 (all three bits)
%   binary()             = 3 (bits 0+1: empty + nonempty byte-aligned)
%   nonempty_bitstring() = 6 (bits 1+2: nonempty byte-aligned + non-byte-aligned)
%   nonempty_binary()    = 2 (bit 1 only)
%   <<>>                 = 1 (bit 0 only)

-export([
  reorder/1,
  compare/2,
  empty/0,
  any/0,
  binary/0,
  nonempty_binary/0,
  nonempty_bitstring/0,
  empty_bitstring/0,
  from_m_n/2,
  union/2,
  intersect/2,
  difference/2,
  negate/1,
  is_any/1,
  is_empty/2,
  normalize/3,
  unparse/2,
  all_variables/2,
  has_negative_only_line/1
]).

-include("erlang_types.hrl").

-export_type([type/0]).

-define(UNIVERSE, 7). % 1 bor 2 bor 4

-opaque type() :: 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7.

-spec reorder(X) -> X when X :: type().
reorder(X) -> X.

-spec compare(T, T) -> eq | lt | gt when T :: type().
compare(X, X) -> eq;
compare(X, Y) when X < Y -> lt;
compare(X, Y) when X > Y -> gt.

-spec empty() -> type().
empty() -> 0.

-spec any() -> type().
any() -> ?UNIVERSE.

-spec binary() -> type().
binary() -> 3. % 1 bor 2

-spec nonempty_binary() -> type().
nonempty_binary() -> 2.

-spec nonempty_bitstring() -> type().
nonempty_bitstring() -> 6. % 2 bor 4

-spec empty_bitstring() -> type().
empty_bitstring() -> 1.

% Construct bitstring type from <<_:M, _:_*N>> parameters.
% M = base size in bits (non-negative integer)
% N = unit size in bits (non-negative integer)
% Possible sizes: {M + K*N | K >= 0} (or just {M} if N = 0)
-spec from_m_n(non_neg_integer(), non_neg_integer()) -> type().
from_m_n(0, 0) -> 1; % only empty bitstring
from_m_n(M, 0) when M > 0 ->
  case M rem 8 of
    0 -> 2; % nonempty byte-aligned
    _ -> 4  % nonempty non-byte-aligned
  end;
from_m_n(M, N) ->
  compute_bits(M, N, 0, 0).

-spec compute_bits(non_neg_integer(), pos_integer(), type(), non_neg_integer()) -> type().
compute_bits(_M, _N, ?UNIVERSE, _K) -> ?UNIVERSE; % early exit: all bits set
compute_bits(_M, _N, Bits, 9) -> Bits; % checked K = 0..8, covers full residue cycle
compute_bits(M, N, Bits, K) ->
  Size = M + K * N,
  NewBit = case {Size, Size rem 8} of
    {0, _} -> 1; % empty bitstring
    {_, 0} -> 2; % nonempty byte-aligned
    {_, _} -> 4  % nonempty non-byte-aligned
  end,
  compute_bits(M, N, Bits bor NewBit, K + 1).

-spec union(T, T) -> T when T :: type().
union(X, Y) -> X bor Y.

-spec intersect(T, T) -> T when T :: type().
intersect(X, Y) -> X band Y.

-spec difference(T, T) -> T when T :: type().
difference(X, Y) -> X band (?UNIVERSE bxor Y).

-spec negate(T) -> T when T :: type().
negate(X) -> ?UNIVERSE bxor X.

-spec is_any(type()) -> boolean().
is_any(?UNIVERSE) -> true;
is_any(_) -> false.

-spec is_empty(type(), T) -> {boolean(), T}.
is_empty(0, S) -> {true, S};
is_empty(_, S) -> {false, S}.

-spec normalize(type(), _, T) -> {constraint_set:set_of_constraint_sets(), T}.
normalize(Dnf, _, ST) ->
  case is_empty(Dnf, #{}) of
    {true, _} -> {constraint_set:sat(), ST};
    {false, _} -> {constraint_set:unsat(), ST}
  end.

-spec unparse(type(), T) -> {ast_ty(), T}.
unparse(0, ST) -> {{predef, none}, ST};
unparse(1, ST) -> {{bitstring, 0, 0}, ST};
unparse(2, ST) -> {{bitstring, 8, 8}, ST};
unparse(3, ST) -> {{bitstring, 0, 8}, ST};
unparse(4, ST) -> {{bitstring, 1, 1}, ST}; % overapprox: non-byte-aligned only -> nonempty_bitstring
unparse(5, ST) -> {{bitstring}, ST};       % overapprox: empty | non-byte-aligned -> bitstring()
unparse(6, ST) -> {{bitstring, 1, 1}, ST};
unparse(7, ST) -> {{bitstring}, ST}.

-spec all_variables(type(), all_variables_cache()) -> sets:set(variable()).
all_variables(_, _) -> sets:new().

-spec has_negative_only_line(type()) -> boolean().
has_negative_only_line(_) -> false.
