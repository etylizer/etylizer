#!/usr/bin/env escript
%% Counts type system feature usage across Erlang source files.
%% Uses the Erlang parser to get definite uses (no false positives from grep).

main([Dir]) ->
    Files = filelib:fold_files(Dir, "\\.erl$", true, fun(F, Acc) -> [F | Acc] end, []),
    AllForms = lists:flatmap(fun parse_file/1, Files),

    %% Extract all -spec declarations as [{FunName, Arity, TypeClauses}]
    Specs = everything(
        fun({attribute, _, spec, {{Name, Arity}, Types}}) -> {ok, {Name, Arity, Types}};
           (_) -> error
        end, AllForms),

    %% 1. Union types (T1 | T2) anywhere in specs and type declarations
    Unions = length(everything(
        fun({type, _, union, _}) -> {rec, u}; (_) -> error end,
        AllForms)),

    %% 2. Overloaded specs (more than one clause, i.e. -spec f(A) -> B ; (C) -> D.)
    Overloaded = length([1 || {_, _, Types} <- Specs, length(Types) > 1]),

    %% 3. dynamic() usages
    Dynamics = length(everything(
        fun({type, _, dynamic, []}) -> {ok, d}; (_) -> error end,
        AllForms)),

    %% 4. Polymorphic specs: a type variable must appear 2+ times in the
    %%    function type (not counting `when` constraints) to create a real
    %%    type relationship. Variables that appear once are just aliases.
    Polymorphic = length([1 || {_, _, Types} <- Specs, is_polymorphic(Types)]),

    %% 5. Specs using numeric subtypes
    Numeric = length([1 || {_, _, Types} <- Specs,
        [] =/= everything(fun(T) ->
            case is_numeric_type(T) of true -> {ok, T}; false -> error end
        end, Types)]),

    %% 6. Functions missing a spec (per-file to avoid cross-module collisions)
    MissingSpecs = lists:sum(lists:map(fun(File) ->
        Forms = parse_file(File),
        Funs = sets:from_list(everything(
            fun({function, _, Name, Arity, _}) -> {ok, {Name, Arity}}; (_) -> error end,
            Forms)),
        SpecNames = sets:from_list(everything(
            fun({attribute, _, spec, {{Name, Arity}, _}}) -> {ok, {Name, Arity}}; (_) -> error end,
            Forms)),
        sets:size(sets:subtract(Funs, SpecNames))
    end, Files)),

    %% 8. Occurrence typing
    %% 8a. is_* type-test BIF calls in guard positions
    Guards = everything(
        fun({clause, _, _, G, _}) when G =/= [] -> {ok, G}; (_) -> error end,
        AllForms),
    TypeTests = length(everything(
        fun({call, _, {atom, _, Name}, _}) ->
               case is_type_test(Name) of true -> {rec, Name}; false -> error end;
           ({call, _, {remote, _, {atom, _, erlang}, {atom, _, Name}}, _}) ->
               case is_type_test(Name) of true -> {rec, Name}; false -> error end;
           (_) -> error
        end, Guards)),
    %% 8b. Case clauses whose pattern binds variables (structural refinement)
    AllCaseClauses = lists:flatmap(
        fun({'case', _, _, Clauses}) -> Clauses end,
        everything(
            fun({'case', _, _, _} = C) -> {rec, C}; (_) -> error end,
            AllForms)),
    CaseClauses = length([1 || {clause, _, [Pat], _, _} <- AllCaseClauses,
        [] =/= everything(
            fun({var, _, '_'}) -> error;
               ({var, _, _}) -> {rec, v};
               (_) -> error
            end, Pat)]),
    %% 8c. Functions/cases with > 5 clauses
    ManyClauses = length(everything(
        fun({function, _, _, _, Cls}) when length(Cls) > 5 -> {rec, mc};
           ({'case', _, _, Cls}) when length(Cls) > 5 -> {rec, mc};
           ({'fun', _, {clauses, Cls}}) when length(Cls) > 5 -> {rec, mc};
           ({named_fun, _, _, Cls}) when length(Cls) > 5 -> {rec, mc};
           (_) -> error
        end, AllForms)),
    %% 8d. Guards with > 32 connectives
    ManyConnGuards = length([1 || G <- Guards,
        count_guard_connectives(G) > 32]),
    %% 8e. Enum type alias with > 16 alternatives
    LargeEnums = length(everything(
        fun({attribute, _, type, {_, {type, _, union, Alts}, _}})
              when length(Alts) > 16 -> {ok, e};
           (_) -> error
        end, AllForms)),
    %% 8f. Already-bound variable in pattern
    AllCaseExprs = everything(
        fun({'case', _, _, _} = C) -> {rec, C}; (_) -> error end,
        AllForms),
    BoundVarInCasePat = lists:sum([begin
        SVars = var_names(Scrut),
        case SVars of
            [] -> 0;
            _ ->
                SSet = sets:from_list(SVars),
                length([1 || {clause, _, Pats, _, _} <- Clauses,
                    lists:any(fun(V) -> sets:is_element(V, SSet) end,
                              var_names(Pats))])
        end
    end || {'case', _, Scrut, Clauses} <- AllCaseExprs]),
    BoundVarInFunPat = lists:sum([
        length([1 || {clause, _, Pats, _, _} <- Clauses,
            has_repeated_var(Pats)])
        || Clauses <- everything(
            fun({function, _, _, _, Cls}) -> {ok, Cls}; (_) -> error end,
            AllForms)]),
    BoundVarInPat = BoundVarInCasePat + BoundVarInFunPat,
    %% 8g. Non-linear patterns (same variable bound 2+ times in a clause's patterns)
    NonLinearPats = length([1 || Pats <- everything(
        fun({clause, _, Pats, _, _}) when Pats =/= [] -> {ok, Pats}; (_) -> error end,
        AllForms), has_repeated_var(Pats)]),

    %% 9. receive expressions
    Receives = length(everything(
        fun({'receive', _, _}) -> {rec, r};
           ({'receive', _, _, _, _}) -> {rec, r};
           (_) -> error
        end, AllForms)),

    %% 7. send expressions (Pid ! Msg)
    Sends = length(everything(
        fun({op, _, '!', _, _}) -> {rec, s}; (_) -> error end,
        AllForms)),

    io:format("Union types:           ~b~n", [Unions]),
    io:format("Overloaded specs:      ~b~n", [Overloaded]),
    io:format("dynamic() usages:      ~b~n", [Dynamics]),
    io:format("Polymorphic specs:     ~b~n", [Polymorphic]),
    io:format("Numeric subtype specs: ~b~n", [Numeric]),
    io:format("Missing specs:         ~b~n", [MissingSpecs]),
    io:format("Type guards (is_*):    ~b~n", [TypeTests]),
    io:format("Case refinements:      ~b~n", [CaseClauses]),
    io:format(">5 clauses:            ~b~n", [ManyClauses]),
    io:format(">32 guard connectives: ~b~n", [ManyConnGuards]),
    io:format(">16 enum alternatives: ~b~n", [LargeEnums]),
    io:format("Bound var in pattern:  ~b~n", [BoundVarInPat]),
    io:format("Non-linear patterns:   ~b~n", [NonLinearPats]),
    io:format("receive expressions:   ~b~n", [Receives]),
    io:format("send expressions:      ~b~n", [Sends]),
    Modules = length(everything(
        fun({attribute, _, module, _}) -> {ok, m}; (_) -> error end,
        AllForms)),
    io:format("(~b files scanned, ~b modules, ~b specs total)~n",
              [length(Files), Modules, length(Specs)]);
main(_) ->
    io:format("Usage: count_unions.escript <directory>~n").

%% --- helpers ---

-spec parse_file(file:filename()) -> [term()].
parse_file(File) ->
    case epp_dodger:quick_parse_file(File) of
        {ok, Forms} -> [erl_syntax:revert(F) || F <- Forms];
        {error, _} -> []
    end.

%% A spec is polymorphic if any type variable appears 2+ times in the
%% function signature of any clause. For bounded_fun (specs with `when`),
%% only the fun type is inspected, not the constraints.
-spec is_polymorphic([term()]) -> boolean().
is_polymorphic(TypeClauses) ->
    lists:any(fun is_clause_polymorphic/1, TypeClauses).

-spec is_clause_polymorphic(term()) -> boolean().
is_clause_polymorphic({type, _, bounded_fun, [FunType, _Constraints]}) ->
    has_repeated_var(FunType);
is_clause_polymorphic(FunType) ->
    has_repeated_var(FunType).

-spec has_repeated_var(term()) -> boolean().
has_repeated_var(FunType) ->
    Vars = everything(
        fun({var, _, '_'}) -> error;
           ({var, _, Name}) -> {ok, Name};
           (_) -> error
        end, FunType),
    length(Vars) =/= length(lists:usort(Vars)).

-spec is_type_test(atom()) -> boolean().
is_type_test(Name) ->
    lists:member(Name, [
        is_atom, is_binary, is_bitstring, is_boolean, is_float,
        is_function, is_integer, is_list, is_map, is_number,
        is_pid, is_port, is_record, is_reference, is_tuple
    ]).

-spec is_numeric_type(term()) -> boolean().
is_numeric_type({type, _, Name, []}) ->
    lists:member(Name, [integer, non_neg_integer, pos_integer, neg_integer,
                        byte, char, arity]);
is_numeric_type({type, _, range, _}) -> true;
is_numeric_type({integer, _, _}) -> true;
is_numeric_type(_) -> false.

-spec var_names(term()) -> [atom()].
var_names(Term) ->
    everything(
        fun({var, _, '_'}) -> error;
           ({var, _, Name}) -> {ok, Name};
           (_) -> error
        end, Term).

-spec count_guard_connectives([[term()]]) -> non_neg_integer().
count_guard_connectives(GuardSeqs) ->
    Semis = max(0, length(GuardSeqs) - 1),
    Commas = lists:sum([max(0, length(Seq) - 1) || Seq <- GuardSeqs]),
    Nested = length(everything(
        fun({op, _, 'andalso', _, _}) -> {rec, c};
           ({op, _, 'orelse', _, _}) -> {rec, c};
           (_) -> error
        end, GuardSeqs)),
    Semis + Commas + Nested.

-spec everything(fun((term()) -> {ok, T} | {rec, T} | error), term()) -> [T].
everything(F, T) ->
    Recurse = fun() ->
        case T of
            X when is_list(X) -> lists:flatmap(fun(E) -> everything(F, E) end, X);
            X when is_tuple(X) -> lists:flatmap(fun(E) -> everything(F, E) end, tuple_to_list(X));
            X when is_map(X) -> lists:flatmap(fun(E) -> everything(F, E) end, maps:to_list(X));
            _ -> []
        end
    end,
    case F(T) of
        error -> Recurse();
        {ok, X} -> [X];
        {rec, X} -> [X | Recurse()]
    end.
