-module(representation_tests).

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
      {ty_key,'.','a',0} => {ty_scheme,[], {mu, {mu_var,'$node_2'}, {tuple,[{mu_var,'$node_2'}]}} },
      {ty_key,'.','b',0} => {ty_scheme,[], {mu, {mu_var,'$node_1'}, {tuple,[{mu_var,'$node_1'}]}} }
     }).

share_same_name_after_unparse_test() ->
  with_symtab(
    fun() -> 
        A = ty_parser:parse(tnamed(a)),
        X = ty_node:is_empty(A),
        Eval = ty_parser:unparse(A),
        io:format(user,"Unparsed~n~p~n", [Eval]),
        AA = ty_parser:parse(Eval),
        X = ty_node:is_empty(AA),
        ok
    end,
    #{ 
      {ty_key,'.','a',0} => 
      {ty_scheme,[], {tuple,[ {named,0,{ty_ref,'.','a',0},[]} ]}}
     }).

% we have support for detecting isomorphic locally anonymous recursive type via DeBrujin indices
% but no support for detecting isomorphic named types
share_isomorphic_recursive_types_test() ->
  global_state:with_new_state(fun() ->
    % TODO test case with two isomorphic recursive types, and implement isomorphic detection
    ok
  end).

debug_mu_test() ->
  with_symtab(
    fun() -> 
        A = ty_parser:parse(tnamed(a)),
        io:format(user,"Parsed~n~p~n~p~n", [A, ty_node:dump(A)]),
        X = ty_node:is_empty(A),
        Eval = ty_parser:unparse(A),
        AA = ty_parser:parse(Eval),
        io:format(user,"Parsed~n~p~n~p~n", [AA, ty_node:dump(AA)]),
        X = ty_node:is_empty(AA),
        ok
    end,
    #{ 
      {ty_key,'.','a',0} => 
      {ty_scheme,[], {tuple,[ {named,0,{ty_ref,'.','a',0},[]} ]}}
     }).

debug_parser_test() ->
  with_symtab(
    fun() -> 
        A = ty_parser:parse(tnamed(a)),
        io:format(user,"~p~n~p~n", [A, ty_node:dump(A)]),
        X = ty_node:is_empty(A),
        io:format(user,"Unparsing start: ~p~n", [A]),
        Eval = ty_parser:unparse(A),
        io:format(user,"~p~n", [Eval]),
        AA = ty_parser:parse(Eval),
        io:format(user,"Reparse~n~p~n~p~n", [AA, ty_node:dump(AA)]),
        X = ty_node:is_empty(AA),
        ok
    end,
#{
  {ty_key,'.','a',0} => 
    {ty_scheme,[],
     {union,[
             {tuple,[
                     {union,[
                             {named,0,{ty_ref,'.','a',0},[]},
                             {var,alpha}
                            ]},
                     {intersection,[
                                    {named,0,{ty_ref,'.','a',0},[]},
                                    {var,alpha}
                                   ]}
                    ]},
             {tuple,[{named,0,{ty_ref,'.','a',0},[]}]}
            ]}}
 }
   ).

% This is an invalid type (a duplicate mu_var should map to the same body, otherwise the parser errors out)
% The unparser has to guarantee that a type equation produces the same body for the same binder
debug_unparse_test() ->
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
        io:format(user,"Fin~n~p~n~p~n", [Parsed, ty_node:dump(Parsed)]),
        %Eval = ty_parser:unparse(Parsed),
        %io:format(user,"~p~n", [Eval]),
        ok
    end,
#{}).

debug_parse2_test() ->
  with_symtab(
    fun() -> 
        Node = 
{mu, {mu_var,'$node_1'},
 {tuple,
      [{mu, {mu_var,'$node_2'},
        {tuple, [{singleton, a}, {mu_var,'$node_1'}]}
       },
       {mu, {mu_var,'$node_2'},
        {tuple, [{singleton, b}, {mu_var,'$node_2'}]}
       },
       {mu, {mu_var,'$node_2'},
        {tuple, [{singleton, b}, {mu_var,'$node_2'}]}
       }
      ]
 }},
        Parsed = ty_parser:parse(Node),
        io:format(user,"Fin~n~p~n~p~n", [Parsed, ty_node:dump(Parsed)]),
        %Eval = ty_parser:unparse(Parsed),
        %io:format(user,"~p~n", [Eval]),
        ok
    end,
#{}).
