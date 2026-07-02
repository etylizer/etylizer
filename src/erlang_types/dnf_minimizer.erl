% Single-pass two-level DNF minimizer over a cube list.
% Core of espresso, single-pass, only heuristics.
%
% * compute off-set as the Shannon complement of the on-set cover
% * expand each on-cube to a prime implicant against that off-set
% * drop the redundant ones
%
% Internally a cube is a positional bignum spanning 2*NumVars + NumLeaves bits:
% variable V owns bit 2V (the value-0 literal) and 2V+1 (the value-1 literal);
% leaf J owns bit 2*NumVars + J.
-module(dnf_minimizer).
-export([minimize/3]).

-record(config, {num_vars        :: non_neg_integer(),
                 num_leaves      :: non_neg_integer(),
                 dimension_masks :: [non_neg_integer()],
                 full_mask       :: non_neg_integer(),
                 even_mask       :: non_neg_integer(),
                 output_mask     :: non_neg_integer()}).

-spec minimize(non_neg_integer(), non_neg_integer(),
               [{[non_neg_integer()], [non_neg_integer()], [non_neg_integer()]}]) ->
          [{[non_neg_integer()], [non_neg_integer()], [non_neg_integer()]}].
minimize(NumVars, NumLeaves, OnSet) ->
    Config = make_config(NumVars, NumLeaves),
    EncodedOnSet = [encode(Config, Cube) || Cube <- OnSet],
    OffSet = complement(Config, 0, EncodedOnSet),
    [decode(Config, Cube) || Cube <- irredundant(Config, [], expand(Config, OffSet, EncodedOnSet))].

complement(Config, _Cofactor, []) -> [Config#config.full_mask];       % empty cover -> universe
complement(Config, Cofactor, [Cube]) -> complement_cube(Config, Cofactor bor Cube); % single cube -> De Morgan
complement(Config, Cofactor, Cubes) ->
    FullMask = Config#config.full_mask,
    Ceiling = lists:foldl(fun(Cube, Acc) -> Acc bor Cube end, Cofactor, Cubes),
    maybe
        false ?= lists:any(fun(Cube) -> (Cube bor Cofactor) =:= FullMask end, Cubes), % a full row
        true ?= (Ceiling =:= FullMask), % an all-zero column
        {_, _, LowMask, HighMask, CofactorLow, CofactorHigh, LeftCubes, RightCubes} =
            shannon(Config, Cofactor, Cubes),
        [Complement band LowMask || Complement <- complement(Config, CofactorLow, LeftCubes)] ++
        [Complement band HighMask || Complement <- complement(Config, CofactorHigh, RightCubes)]
    else
        true  -> []; % full row -> empty
        false -> complement(Config, Cofactor bor (FullMask bxor Ceiling), Cubes)
                 ++ complement_cube(Config, Ceiling)
    end.

% De Morgan complement of a single cube: one cube per variable it does not fill
complement_cube(Config, Cube) ->
    FullMask = Config#config.full_mask,
    [FullMask bxor (Mask band Cube) || Mask <- Config#config.dimension_masks, (Mask band Cube) =/= Mask].

% {Positives, Negatives, Leaves} <-> positional bignum
encode(Config, {Positives, Negatives, Leaves}) ->
    NumVars = Config#config.num_vars,
    Fixed = Positives ++ Negatives,
    DontCareBits = lists:foldl(
        fun(Var, Acc) ->
            case lists:member(Var, Fixed) of
                true -> Acc;
                false -> Acc bor (3 bsl (2 * Var))
            end
        end, 0, lists:seq(0, NumVars - 1)),
    lists:foldl(fun(Var, Acc) -> Acc bor (1 bsl (2 * Var + 1)) end, DontCareBits, Positives)
        bor lists:foldl(fun(Var, Acc) -> Acc bor (1 bsl (2 * Var)) end, 0, Negatives)
        bor lists:foldl(fun(Leaf, Acc) -> Acc bor (1 bsl (2 * NumVars + Leaf)) end, 0, Leaves).

decode(Config, Cube) ->
    NumVars = Config#config.num_vars,
    NumLeaves = Config#config.num_leaves,
    {[Var || Var <- lists:seq(0, NumVars - 1), test_bit(Cube, 2 * Var + 1), not test_bit(Cube, 2 * Var)],
     [Var || Var <- lists:seq(0, NumVars - 1), test_bit(Cube, 2 * Var), not test_bit(Cube, 2 * Var + 1)],
     [Leaf || Leaf <- lists:seq(0, NumLeaves - 1), test_bit(Cube, 2 * NumVars + Leaf)]}.

% smallest cubes first, skip ones absorbed by a produced prime
expand(Config, OffSet, Cubes) ->
    SmallestFirst = [Cube || {_, Cube} <- lists:sort([{bit_count(Cube), Cube} || Cube <- Cubes])],
    expand_loop(Config, OffSet, SmallestFirst, []).

expand_loop(_Config, _OffSet, [], Primes) -> Primes;
expand_loop(Config, OffSet, [Cube | Rest], Primes) ->
    case lists:any(fun(Prime) -> implies(Cube, Prime) end, Primes) of
        true  -> expand_loop(Config, OffSet, Rest, Primes);
        false -> expand_loop(Config, OffSet, Rest, [expand_cube(Config, OffSet, Cube) | Primes])
    end.

expand_cube(Config, OffSet, Cube) ->
    FullMask = Config#config.full_mask,
    raise_loop(OffSet, Cube, FullMask bxor Cube, FullMask,
               Config#config.even_mask, Config#config.output_mask).

raise_loop(OffSet, Raised, FreeBits, FullMask, EvenMask, OutputMask) ->
    Feasible = FreeBits band (FullMask bxor blocked(OffSet, Raised, EvenMask, OutputMask, 0)),
    case Feasible of
        0 -> Raised;
        _ -> Bit = lowest_set_bit(Feasible),
             raise_loop(OffSet, Raised bor (1 bsl Bit), Feasible band bnot (1 bsl Bit),
                        FullMask, EvenMask, OutputMask)
    end.

blocked([], _Raised, _EvenMask, _OutputMask, Blocked) -> Blocked;
blocked([OffCube | Rest], Raised, EvenMask, OutputMask, Blocked) ->
    Overlap = Raised band OffCube,
    ConflictBits = EvenMask bxor ((Overlap bor (Overlap bsr 1)) band EvenMask),
    case Overlap band OutputMask of
        0 when ConflictBits =:= 0 ->
            blocked(Rest, Raised, EvenMask, OutputMask, Blocked bor OutputMask);
        0 ->
            blocked(Rest, Raised, EvenMask, OutputMask, Blocked);
        _ when ConflictBits =/= 0, (ConflictBits band (ConflictBits - 1)) =:= 0 ->
            blocked(Rest, Raised, EvenMask, OutputMask,
                    Blocked bor (OffCube band (3 bsl lowest_set_bit(ConflictBits))));
        _ ->
            blocked(Rest, Raised, EvenMask, OutputMask, Blocked)
    end.

% keep only cubes not covered by the rest (tautology of the cofactor)
irredundant(Config, DontCares, Cubes) -> irredundant_loop(Config, DontCares, [], Cubes).

irredundant_loop(_Config, _DontCares, Kept, []) -> Kept;
irredundant_loop(Config, DontCares, Kept, [Cube | Rest]) ->
    case covered(Config, Cube, Kept ++ Rest ++ DontCares) of
        true  -> irredundant_loop(Config, DontCares, Kept, Rest);
        false -> irredundant_loop(Config, DontCares, Kept ++ [Cube], Rest)
    end.

covered(Config, Cube, Others) ->
    is_tautology(Config, Config#config.full_mask bxor Cube,
                 [Other || Other <- Others, distance(Config, Other, Cube) =:= 0]).

is_tautology(Config, Cofactor, Cubes) ->
    FullMask = Config#config.full_mask,
    maybe
        % a cube that is all-don't-care here already covers everything -> tautology
        false ?= lists:any(fun(Cube) -> (Cube bor Cofactor) =:= FullMask end, Cubes),
        % empty cover -> not a tautology
        true ?= (Cubes =/= []),
        % a bit set in no cube (all-zero column) -> some literal never appears -> not a tautology
        true ?= (lists:foldl(fun(Cube, Acc) -> Acc bor Cube end, Cofactor, Cubes) =:= FullMask),
        % unate base case: <= 1 variable still constrained -> tautology
        false ?= (active_variables(Config, Cofactor, Cubes) =< 1),
        % otherwise Shannon-split on the most binate variable; tautology iff both cofactors are
        {_, _, _, _, CofactorLow, CofactorHigh, LeftCubes, RightCubes} = shannon(Config, Cofactor, Cubes),
        is_tautology(Config, CofactorLow, LeftCubes) andalso is_tautology(Config, CofactorHigh, RightCubes)
    end.

active_variables(Config, Cofactor, Cubes) ->
    length([1 || Mask <- Config#config.dimension_masks,
                 lists:any(fun(Cube) -> ((Cube bor Cofactor) band Mask) =/= Mask end, Cubes)]).

% Shannon split (chooses the most-binate splittable variable)
shannon(Config, Cofactor, Cubes) ->
    FullMask = Config#config.full_mask,
    SplitVar = split_variable(Config, Cofactor, Cubes),
    SplitMask = lists:nth(SplitVar + 1, Config#config.dimension_masks),
    ActiveBits = [Bit || Bit <- bit_positions(SplitMask), not test_bit(Cofactor, Bit)],
    {LowBits, HighBits} = lists:split(length(ActiveBits) div 2, ActiveBits),
    BitsToMask = fun(Bits) -> lists:foldl(fun(Bit, Acc) -> Acc bor (1 bsl Bit) end, 0, Bits) end,
    LowMask = (FullMask bxor SplitMask) bor BitsToMask(LowBits),
    HighMask = (FullMask bxor SplitMask) bor BitsToMask(HighBits),
    {SplitVar, SplitMask, LowMask, HighMask,
     Cofactor bor (FullMask bxor LowMask), Cofactor bor (FullMask bxor HighMask),
     [Cube || Cube <- Cubes, (Cube band LowMask band SplitMask) =/= 0],
     [Cube || Cube <- Cubes, (Cube band HighMask band SplitMask) =/= 0]}.

split_variable(Config, Cofactor, Cubes) ->
    FullMask = Config#config.full_mask,
    Masks = Config#config.dimension_masks,
    {_, SplitVar} = lists:max(
        [{length([1 || Cube <- Cubes, ((Cube bor Cofactor) band Mask) =/= Mask]), VarIndex}
         || {VarIndex, Mask} <- lists:zip(lists:seq(0, length(Masks) - 1), Masks),
            bit_count(Mask band FullMask) - bit_count(Mask band Cofactor) > 1]),
    SplitVar.

% config + bit utilities
make_config(NumVars, NumLeaves) ->
    #config{num_vars = NumVars,
            num_leaves = NumLeaves,
            dimension_masks = [3 bsl (2 * Var) || Var <- lists:seq(0, NumVars - 1)]
                              ++ [((1 bsl NumLeaves) - 1) bsl (2 * NumVars)],
            full_mask = (1 bsl (2 * NumVars + NumLeaves)) - 1,
            even_mask = lists:foldl(fun(Var, Acc) -> Acc bor (1 bsl (2 * Var)) end, 0, lists:seq(0, NumVars - 1)),
            output_mask = ((1 bsl NumLeaves) - 1) bsl (2 * NumVars)}.

distance(Config, CubeA, CubeB) ->
    EvenMask = Config#config.even_mask,
    Overlap = CubeA band CubeB,
    OutputDistance = case Overlap band Config#config.output_mask of 0 -> 1; _ -> 0 end,
    bit_count(EvenMask bxor ((Overlap bor (Overlap bsr 1)) band EvenMask)) + OutputDistance.

implies(Cube, Prime) -> (Cube band Prime) =:= Cube.

test_bit(Value, Index) -> (Value band (1 bsl Index)) =/= 0.

bit_count(Value) -> bit_count(Value, 0).
bit_count(0, Count) -> Count;
bit_count(Value, Count) -> bit_count(Value band (Value - 1), Count + 1).

lowest_set_bit(Value) -> lowest_set_bit(Value, 0).
lowest_set_bit(Value, Index) ->
    case Value band (1 bsl Index) of 0 -> lowest_set_bit(Value, Index + 1); _ -> Index end.

bit_positions(0) -> [];
bit_positions(Value) -> [lowest_set_bit(Value) | bit_positions(Value band (Value - 1))].

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

%% is_tautology: one test per branch (2 vars a,b; one output; PLA cube in comment)
is_tautology_full_row_test() ->                                 
    % -- 1
    C = make_config(2, 1),
    ?assert(is_tautology(C, 0, [encode(C, {[], [], [0]})])).

is_tautology_empty_test() ->                                    
    % (no cubes)
    C = make_config(2, 1),
    ?assertNot(is_tautology(C, 0, [])).

is_tautology_zero_column_test() ->                              
    % 00 1 
    % 01 1
    C = make_config(2, 1),
    ?assertNot(is_tautology(C, 0, [encode(C, {[], [0, 1], [0]}), encode(C, {[1], [0], [0]})])).

is_tautology_unate_test() ->                                    
    % 0- 1 
    % 1- 1
    C = make_config(2, 1),
    ?assert(is_tautology(C, 0, [
                                encode(C, {[], [0], [0]}), 
                                encode(C, {[0], [], [0]})])).

is_tautology_split_true_test() ->                               
    % 0- 1 
    % -0 1 
    % 11 1
    C = make_config(2, 1),
    ?assert(is_tautology(C, 0, [encode(C, {[], [0], [0]}), encode(C, {[], [1], [0]}),
                                encode(C, {[0, 1], [], [0]})])).

is_tautology_split_false_test() ->                              
    % 0- 1
    % -0 1
    C = make_config(2, 1),
    ?assertNot(is_tautology(C, 0, [encode(C, {[], [0], [0]}), encode(C, {[], [1], [0]})])).

complement_single_test() ->                                     
    % complement of {a=0} = {a=1}
    C = make_config(1, 1),
    ?assertEqual([{[0], [], [0]}], [decode(C, X) || X <- complement(C, 0, [encode(C, {[], [0], [0]})])]).

%% shannon
shannon_split_on_a_test() ->                                    
    % 0- 1
    % 1- 1
    % split on var 0
    C = make_config(2, 1),
    {SplitVar, _, _, _, _, _, Left, Right} =
        shannon(C, 0, [encode(C, {[], [0], [0]}), encode(C, {[0], [], [0]})]),
    ?assertEqual(0, SplitVar),
    ?assertEqual([{[], [0], [0]}], [decode(C, X) || X <- Left]),    % a=0 cube -> low cofactor
    ?assertEqual([{[0], [], [0]}], [decode(C, X) || X <- Right]).   % a=1 cube -> high cofactor

shannon_split_on_b_test() ->                                    
    % -0 1
    % -1 1 
    % split on var 1
    C = make_config(2, 1),
    {SplitVar, _, _, _, _, _, _, _} =
        shannon(C, 0, [encode(C, {[], [1], [0]}), encode(C, {[1], [], [0]})]),
    ?assertEqual(1, SplitVar).
-endif.
