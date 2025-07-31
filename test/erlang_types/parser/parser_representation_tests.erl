-module(parser_representation_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

variable_test() ->
  global_state:with_new_state(fun() ->
    Ty = ty_parser:parse({var, alpha}),
    Tyy = ty_node:dump(Ty),
    #{{node, 1} := {node, _, {leaf, Any}, {leaf, Empty}}} = Tyy,
    gt = ty_rec:compare(Any, Empty),
    ok
  end).

% {leaf,0},#{1 => {leaf,0}} should simplify to {{leaf,0},#{}}
redundant_default_test() ->
  global_state:with_new_state(fun() ->
    Ty = ty_parser:parse(f([tany()], tany())),
    Ty2 = ty_node:negate(Ty),
    Ty3 = ty_node:intersect(Ty, Ty2),
    true = dnf_ty_variable:empty() =:= ty_node:load(Ty3)
  end).

% parser should map sub-structures of a recursive type to the same ID
% across parse passes
share_sub_recursive_types_test() ->
  {ok, [System]} = file:consult("test_files/erlang_types/parser/system_rec"),
  with_symtab(fun() -> 
    Ty = ty_parser:parse(tnamed(ty)),
    Ty2 = ty_parser:parse(tnamed(ty_tuple)),
    true = Ty =:= ty_node:union(Ty, Ty2),
    ok
  end, System).

share_same_recursive_types_test() ->
  {ok, [System]} = file:consult("test_files/erlang_types/parser/system_rec"),
  with_symtab(fun() -> 
    Ty = ty_parser:parse(tnamed(ty)),
    Ty2 = ty_parser:parse(u([tnamed(ty)])),
    true = Ty =:= Ty2,
    ok
  end, System).

% types parsed to the same structure should be shared
% across parse passes
share_simple_types_test() ->
  global_state:with_new_state(fun() ->
    Ty2 = ty_parser:parse(ttuple1(i([b(foo)]))),
    Ty2 = ty_parser:parse(ttuple1(b(foo))),
    ok
  end).

share_simple_types_2_test() ->
  global_state:with_new_state(fun() ->
    Ty = ttuple1(b(foo)),
    TyParsed = ty_parser:parse(Ty),

    Ty2 = ttuple1(u([b(foo)])),
    TyParsed = ty_parser:parse(Ty2),
    TyParsed = ty_parser:parse(Ty2),
    ok
  end).

share_topological_recursive_types_test() ->
  {ok, [System]} = file:consult("test_files/erlang_types/parser/system_topological"),
  with_symtab(fun() ->
    Ty = {tuple, [
      {tuple, [{tuple, [{tuple, [{singleton, bar}, {singleton ,foo}]}]}]},
      {tuple, [{tuple, [{named, noloc, {ty_ref, '.', c, 0}, []}]}]},
      {named, noloc, {ty_ref, '.', e, 0}, []}
    ]},
    TyP = ty_parser:parse(Ty),

    Ty2 = {tuple, [ % root
      {intersection, [{tuple, [{tuple, [{tuple, [{singleton, bar}, {singleton ,foo}]}]}]}]}, %a %b % d, k
      {intersection, [{tuple, [{tuple, [{named, noloc, {ty_ref, '.', c, 0}, []}]}]}]}, % f, c
      {intersection, [{named, noloc, {ty_ref, '.', e, 0}, []}]} % e
    ]},
    TyP = ty_parser:parse(Ty2),
    ok
  end, System).

share_local_isomorphic_recursion_test() ->
  with_symtab(
    fun() -> 
        A = ty_parser:parse(tnamed(a)),
        Eval = ty_parser:unparse(A),
        AA = ty_parser:parse(Eval),

        B = ty_parser:parse(tnamed(b)),
        Eval2 = ty_parser:unparse(B),
        AA = ty_parser:parse(Eval2),
        ok
    end,
    #{ 
      {ty_key,'.','a',0} => {ty_scheme,[], {mu, {mu_var,'aasd'}, {tuple,[{mu_var,'aasd'}]}} },
      {ty_key,'.','b',0} => {ty_scheme,[], {mu, {mu_var,'bd'}, {tuple,[{mu_var,'bd'}]}} }
     }).

share_same_name_after_unparse_test() ->
  with_symtab(
    fun() -> 
        Named = tnamed(a),
        A = ty_parser:parse(Named),
        Named = ty_parser:unparse(A),
        ok
    end,
    #{ 
      {ty_key,'.','a',0} => 
      {ty_scheme,[], {tuple,[ {named,{loc,"AUTO", -1, -1},{ty_ref,'.','a',0},[]} ]}}
     }).

% TODO
% we have support for detecting isomorphic locally anonymous recursive type via DeBrujin indices
% but no support for detecting isomorphic named types
share_isomorphic_recursive_types_test() ->
  with_symtab(
  fun() -> 
    _Node = 
      {mu, {mu_var,'$node_1'},
        {mu, {mu_var,'$node_2'},
             {tuple, [{singleton, b}, {mu_var,'$node_2'}]}
            }},
    % Parsed = ty_parser:parse(Node),
    % io:format(user,"~n=============~nFin~n~p~n~p~n", [Parsed, ty_node:dump(Parsed)]),
    %
    % Eval = ty_parser:unparse(Parsed),
    % io:format(user,"~p~n", [Eval]),
    %
    %
    % Parsed2 = ty_parser:parse(Eval),
    % io:format(user,"~n=============~nFin~n~p~n~p~n", [Parsed2, ty_node:dump(Parsed2)]),
    % Eval2 = ty_parser:unparse(Parsed2),
    % io:format(user,"~p~n", [Eval2]),

    ok
  end,
  #{}).

% just for debugging
% debug_parser_test() ->
%   with_symtab(
%     fun() -> 
%         % check if b can be reverse mapped even though its contained only as a sub-term in a
%         ty_parser:parse(tnamed(a)),
%         % TODO unstable test, how to get the node for {named, 'b'} without parsing it?
%         Named = tnamed(b),
%         Named = ty_parser:unparse({node, 4}),
%         ok
%     end,
%   #{
%     {ty_key,'.','b',0} => {ty_scheme, [], {var, alpha}},
%     {ty_key,'.','a',0} => {ty_scheme,[],
%       {union,[{tuple,[{union,[
%         {named,{loc,"AUTO", -1, -1},{ty_ref,'.','a',0},[]},
%         {named,{loc,"AUTO", -1, -1},{ty_ref,'.','b',0},[]}
%       ]}, 
%       {intersection,[
%         {named,{loc,"AUTO", -1, -1},{ty_ref,'.','a',0},[]},
%         {named,{loc,"AUTO", -1, -1},{ty_ref,'.','b',0},[]}
%       ]}]},
%       {tuple,[{named,{loc,"AUTO", -1, -1},{ty_ref,'.','a',0},[]}]} ]}} 
%    }).

mu_overlap_test() ->
  with_symtab(
    fun() -> 
      Node = 
        {mu, {mu_var,'$node_1'},
          {tuple, [
            {mu, {mu_var,'$node_2'}, {tuple, [{mu_var,'$node_2'}]} }, 
            {mu, {mu_var,'$node_3'}, {union, [
              {tuple, [{mu_var,'$node_3'}]}, 
              {tuple, [
                {mu, {mu_var,'$node_2'}, {union, [
                    {tuple,[{mu_var,'$node_3'}]}, {tuple,[{mu_var,'$node_2'}]}
                ]}}, 
                {mu_var,'$node_3'}
              ]}]}
            }]
          }
        },
      Parsed = ty_parser:parse(Node),
      4 = length(maps:keys(ty_node:dump(Parsed))),
      ok
    end,
  #{}).

parse_bug_test() ->
  {ok, [ListToParse]} = file:consult("test_files/erlang_types/parser/ast_bug"),
  {ok, [Tab]} = file:consult("test_files/erlang_types/parser/ast_bug.tab"),
  % io:format(user, "~p~n", [Tab]),
  
  with_symtab(fun() -> 
    [ty_parser:parse(RawTy) || RawTy <- ListToParse],
    ok
  end, Tab).

parse_bug2_test() ->
  {ok, [ListToParse]} = file:consult("test_files/erlang_types/parser/ast_bug2"),
  global_state:with_new_state(fun() ->
    [ty_parser:parse(RawTy) || RawTy <- ListToParse],
    ok
                 end).

dnf_explosion_test_() ->
  {timeout, 45, fun() ->
  % extract the DNF for the map part of a type
  Dnf = fun(Tyy) -> 
    {leaf, Ty} = ty_node:load(Tyy),
    Z = ty_rec:pi(Ty, dnf_ty_map), 
    _DnfList = dnf_ty_map:dnf(Z)
        end,
  Print = fun(R) -> 
    {TT, T} = timer:tc(fun() -> ty_parser:parse(R) end), 
    % unparsing & pretty printing is very slow, but pretty
    % {TT2, T2} = timer:tc(fun() -> ty_parser:unparse(T) end),
    % io:format(user,"~p us~n", [TT2]),
    % io:format(user,"~n~s~n", [pretty:render_ty(T2)])
    % io:format(user,"Dnf clauses: ~p~n", [(Dnf(T))]),
    % io:format(user,"Dnf clauses: ~p~n", [(dnf_ty_tuple:minimize_dnf(Dnf(T)))]),
    Filtered = lists:filter(fun(Line = {P, [], 1}) -> 
                      {Empty, _} = dnf_ty_tuple:is_empty_line(Line, #{}),
                      % io:format(user,"~p~n~p~n", [P, Empty]),
                      not Empty
                  end, dnf_ty_tuple:minimize_dnf(Dnf(T))),
    io:format(user,"Dnf clauses: ~p~n", [length(Filtered)]),
    ok
          end,
  global_state:with_new_state(fun() ->
    R0 = tmap([tmap_field_opt(b(a), tint()), tmap_field_opt(tany(), tany())]), % R0 = { a : Int .. }
    Print(R0),

    % Rn+1 = Rn & ( { bn : Int} | { cn: Int ..})
    FRi = fun(Ri, Bi1, Ci1) -> 
      i([
        Ri,
        u([
           tmap([tmap_field_opt(b(Bi1), tint())]),
           tmap([tmap_field_opt(b(Ci1), tint()), tmap_field_opt(tany(), tany())])
          ])
       ])
          end,

    R1 = FRi(R0, b1, c1),
    Print(R1),

    R2 = FRi(R1, b2, c2),
    Print(R2),

    R3 = FRi(R2, b3, c3),
    Print(R3),

    R4 = FRi(R3, b4, c4),
    Print(R4),

    R5 = FRi(R4, b5, c5),
    R6 = FRi(R5, b6, c6),
    R7 = FRi(R6, b7, c7),
    R8 = FRi(R7, b8, c8),
    R9 = FRi(R8, b9, c9),
    R10 = FRi(R9, b10, c10),
    Print(R10),

    ok
  end) end}.
