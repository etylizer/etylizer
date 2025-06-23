-module(debug_tests).

-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

-define(LOAD, begin [code:ensure_loaded(M) || M <- [
    persistent_term,
    constraint_set,
    dnf_ty_atom, 
    dnf_ty_bitstring,
    dnf_ty_function, 
    dnf_ty_interval, 
    dnf_ty_list, 
    dnf_ty_map,
    dnf_ty_predefined,
    dnf_ty_tuple,
    dnf_ty_variable,
    global_state,
    ty_bool, 
    ty_function, 
    ty_functions, 
    ty_node, 
    ty_parser, 
    ty_rec, 
    ty_tuple, 
    ty_tuples,
    ty_variable,
    ty,
    tarjan,
    utils
  ]]end).

init_per_suite(Config) ->
    % % Load all modules from the project
    % {ok, Modules} = application:get_key(your_app_name, modules),
    % lists:foreach(fun code:ensure_loaded/1, Modules),
    Config.

slow_test_() ->
  {timeout, 60, fun() -> 
    slow_test(),
    ok 
  end}.

tuple_test() ->
  {ok, [System]} = file:consult("system_tuple"),

  global_state:with_new_state(fun() -> 
    maps:foreach(fun(VarName, AstTy) ->
      ty_parser:extend_symtab(VarName, {ty_scheme, [], AstTy})
    end, System),

    Ty1 = {named, noloc, {ty_ref, '.', a, 0}, []},
    Ty2 = {named, noloc, {ty_ref, '.', b, 0}, []},
    [
      begin
        {Time, Ty} = timer:tc(fun() -> ty_parser:parse(TT) end),
        io:format(user,"~p parse> ~p ms~n", [TTN, Time/1000]),
        {Time2, _} = timer:tc(fun() -> ty_node:is_empty(Ty) end),
        io:format(user,"~p is_empty> ~p ms~n", [TTN, Time2/1000])
      end
      || {_,_,{_,_,TTN,_},_} = TT <- [Ty1, Ty2]
    ],

    [
      begin
        {Time, Ty} = timer:tc(fun() -> ty_parser:parse(TT) end),
        io:format(user,"~p parse> ~p ms~n", [TTN, Time/1000]),
        {Time2, _} = timer:tc(fun() -> ty_node:is_empty(Ty) end),
        io:format(user,"~p is_empty> ~p ms~n", [TTN, Time2/1000])
      end
      || {_,_,{_,_,TTN,_},_} = TT <- [Ty1, Ty2]
    ],


    ok
  end).


slow_test() ->
  % {ok, [System]} = file:consult("test_case_for_local_definitions"),
  {ok, [System]} = file:consult("system"),
  ?LOAD,

  global_state:with_new_state(fun() -> 
    AllNames = [begin ty_parser:extend_symtab(VarName, {ty_scheme, [], AstTy}), VarName end  || VarName := AstTy <- System],
    [begin
        {Time, Ty} = timer:tc(fun() -> 
          TT = {named, noloc, {ty_ref, '.', Name, 0}, []},
          Z = ty_parser:parse(TT),
          Z
        end),
        io:format(user,"~p parse> ~p ms~n", [Name, Time/1000]),
        {Time2, _} = timer:tc(fun() -> 
        ty_node:is_empty(Ty) end),
        io:format(user,"~p is_empty> ~p ms~n", [Name, Time2/1000])
      end
      || Name <- AllNames
    ],

    ok
  end).


ast_test() ->
  {ok, [System]} = file:consult("system_ast"),
  % ensure all modules are loaded (takes ~20ms)
  ?LOAD,

  global_state:with_new_state(fun() -> 
    maps:foreach(fun({ty_key,ast,VarName,_Arity}, AstTyScheme) ->
      ty_parser:extend_symtab(VarName, AstTyScheme)
    end, System),

    Ty = {named, noloc, {ty_ref, 'ast', ty, 0}, []},

    {Time, _} = timer:tc(fun() -> 
      % fprof:trace(start),
      Z = ty_parser:parse(Ty),
      % fprof:trace(stop),
      % fprof:profile(),
      % fprof:analyse(),
      Z
    end),
    io:format(user,"parse> ~p ms~n", [Time/1000]),

    ok
  end).


op_test() ->
  {ok, [System]} = file:consult("system_rec"),

  global_state:with_new_state(fun() -> 
    maps:foreach(fun({ty_key,ast,VarName,_Arity}, AstTyScheme) -> ty_parser:extend_symtab(VarName, AstTyScheme) end, System),

    TyRaw = {named, noloc, {ty_ref, 'ast', ty, 0}, []},
    Ty = ty_parser:parse(TyRaw),

    io:format(user,"~n", []),
    io:format(user,"~w~n", [Ty]),
    % [io:format(user,"~w ::~n~w~n", [Node, Rec]) || Node := Rec <- ty_node:dump(Ty)],

    Ty = ty_node:intersect(Ty, Ty),
    io:format(user,"~n", []),
    io:format(user,"~w~n", [Ty]),
    % [io:format(user,"~w ::~n~w~n", [Node, Rec]) || Node := Rec <- ty_node:dump(Ty2)],
    % io:format(user,"~p~n", [Ty2]),

    ok
  end).

norm_test() ->
  {ok, [System]} = file:consult("plus.config"),
  ?LOAD,
  io:format(user,"~n", []),

  global_state:with_new_state(fun() -> 
    maps:foreach(fun(VarName, AstTy) ->
      ty_parser:extend_symtab(VarName, {ty_scheme, [], AstTy})
    end, System),

    T1 = ty_parser:parse(tnamed(plus)),
    T2 = ty_parser:parse(tnamed(vars)),
    SnT1 = ty_node:difference(T1, T2),
    %io:format(user,"~p~n", [ty_node:dump(SnT1)]),
    Norm = ty_node:normalize(SnT1, #{}),
    io:format(user,"======~nNormalized:~n~p~n", [Norm]),

    SnT2 = ty_parser:parse(tnamed(c1)),
    %io:format(user,"~p~n", [ty_node:dump(SnT2)]),
    Norm2 = ty_node:normalize(SnT2, #{}),
    io:format(user,"======~nNormalized:~n~p~n", [Norm2]),


    Meet = constraint_set:meet(Norm, Norm2),
    io:format(user,"======Meet:~n~p~n", [Meet]),


    ok
  end).
  

unparse_slow_test() ->
  {ok, [System]} = file:consult("system_unparse_slow_2"),
  % ensure all modules are loaded (takes ~20ms)
  ?LOAD,

  global_state:with_new_state(fun() -> 
    AllNames = [begin 
                  ty_parser:extend_symtab({ty_key,'.',VarName, 0}, {ty_scheme, [], AstTy}), VarName 
                end  || VarName := AstTy <- System],

    [F | _] = lists:reverse(AllNames),
    io:format(user,"~p~n", [F]),
    TT = {named, noloc, {ty_ref, '.', F, 0}, []},
    Z = ty_parser:parse(TT),
    {Time, _} = 
    timer:tc( 
      fun() -> 
        % fprof:trace(start),
        ZZ = ty_parser:unparse(Z),
        io:format(user,"Printing...~n", []),
        io:format(user,"~w~n", [ZZ]),
        % fprof:trace(stop),
        % fprof:profile(),
        % fprof:analyse(),
        ok
                         end),
    io:format(user,"~p us~n", [Time]),


    % [begin
    %     {Time, Ty} = timer:tc(fun() -> 
    %       TT = {named, noloc, {ty_ref, '.', Name, 0}, []},
    %       Z = ty_parser:parse(TT),
    %       Z
    %     end),
    %     io:format(user,"~p~nparse> ~p ms~n", [Name, Time/1000]),
    %     {Time2, _} = timer:tc(fun() -> 
    %     ty_parser:unparse(Ty) end),
    %     io:format(user,"unparse> ~p ms~n", [Time2/1000])
    %   end
    %   || Name <- AllNames
    % ],

    % Ty = {named, noloc, {ty_ref, 'ast', ty, 0}, []},
    %
    % {Time, _} = timer:tc(fun() -> 
    %   % fprof:trace(start),
    %   Z = ty_parser:parse(Ty),
    %   % fprof:trace(stop),
    %   % fprof:profile(),
    %   % fprof:analyse(),
    %   Z
    % end),
    % io:format(user,"parse> ~p ms~n", [Time/1000]),

    ok
  end).
