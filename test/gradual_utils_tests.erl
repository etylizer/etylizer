-module(gradual_utils_tests).

-include_lib("eunit/include/eunit.hrl").
 
%% -------------------- collect_pos_neg_tyvars/1 tests -----------------------

collect_pos_neg_tyvars_test() ->
    % Construct a type AST where:
    %  - 'A' appears with both even (positive) and odd (negative) negation counts
    %  - 'C' appears with even negation count (positive)
    %  - 'B' and 'D' appear with odd negation counts (negative)
    % This ensures there is at least one tyvar that occurs with both parities.
    Ty = {union, [
              {var, 'A'},                               % even (positive)
              {negation, {var, 'B'}},                   % odd (negative)
              {intersection, [
                  {negation, {negation, {var, 'C'}}},   % even (2 negations) -> positive
                  {negation, {var, 'D'}}                % odd -> negative
              ]},
              {union, [
                  {negation, {var, 'A'}}                % odd (negative) occurrence of 'A'
              ]}
          ]},
    Res = gradual_utils:collect_pos_neg_tyvars(Ty),
    ?assertEqual(sets:from_list(['A'], [{version, 2}]), Res).

no_overlap_all_positive_test() ->
    % All variables occur with even (positive) parity only -> intersection is empty
    Ty = {union, [
              {var, 'P'},
              {intersection, [
                  {var, 'Q'},
                  {negation, {negation, {var, 'R'}}}
              ]}
          ]},
    Res = gradual_utils:collect_pos_neg_tyvars(Ty),
    ?assertEqual(sets:new([{version, 2}]), Res).

no_overlap_all_negative_test() ->
    % All variables occur with odd (negative) parity only -> intersection is empty
    Ty = {union, [
              {negation, {var, 'N1'}},
              {intersection, [
                  {negation, {var, 'N2'}},
                  {negation, {negation, {negation, {var, 'N3'}}}}
              ]}
          ]},
    Res = gradual_utils:collect_pos_neg_tyvars(Ty),
    ?assertEqual(sets:new([{version, 2}]), Res).

function_argument_and_return_parity_test() ->
    Ty = {fun_full, [ {negation, {var, 'X'}} ], {var, 'X'}},
    Res = gradual_utils:collect_pos_neg_tyvars(Ty),
    ?assertEqual(sets:from_list(['X'], [{version, 2}]), Res).

nested_negations_parity_test() ->
    % A variable appearing once positive and once with triple negation -> both parities
    Ty = {union, [ {var, 'Y'}, {negation, {negation, {negation, {var, 'Y'}}}} ]},
    Res = gradual_utils:collect_pos_neg_tyvars(Ty),
    ?assertEqual(sets:from_list(['Y'], [{version, 2}]), Res).

empty_union_test() ->
    % Empty union should yield empty result set
    Ty = {union, []},
    Res = gradual_utils:collect_pos_neg_tyvars(Ty),
    ?assertEqual(sets:new([{version, 2}]), Res).


%% -------------------- subst_ty/3 tests -----------------------

subst_discriminate_framevar_to_dynamic_test() ->
    Sub = #{ '$A' => {var, '%F1'} },
    Ty = {var, '$A'},
    R = gradual_utils:subst_ty(Ty, Sub, discriminate),
    ?assertEqual({predef, dynamic}, R).

subst_discriminate_normal_var_passthrough_test() ->
    Sub = #{ '$A' => {var, '$B'} },
    Ty = {var, '$A'},
    R = gradual_utils:subst_ty(Ty, Sub, discriminate),
    ?assertEqual({var, '$B'}, R).

subst_no_discrimination_keeps_framevar_test() ->
    Sub = #{ '$A' => {var, '%F2'} },
    Ty = {var, '$A'},
    R = gradual_utils:subst_ty(Ty, Sub, no_discrimination),
    ?assertEqual({var, '%F2'}, R).

subst_unknown_var_passthrough_test() ->
    Sub = #{ '$B' => {var, '$C'} },
    Ty = {var, '$A'},
    R = gradual_utils:subst_ty(Ty, Sub, discriminate),
    ?assertEqual({var, '$A'}, R).

subst_union_recursive_test() ->
    Sub = #{ '$A' => {var, '%F3'}, '$B' => {var, '$C'} },
    Ty = {union, [ {var, '$A'}, {var, '$B'} ]},
    R = gradual_utils:subst_ty(Ty, Sub, discriminate),
    ?assertEqual({union, [ {predef, dynamic}, {var, '$C'} ]}, R).

subst_fun_full_recursive_test() ->
    Sub = #{ '$P' => {var, '%F4'}, '$Q' => {var, '$R'} },
    Ty = {fun_full, [ {var, '$P'} ], {union, [ {var, '$Q'}, {var, '$P'} ]}},
    R = gradual_utils:subst_ty(Ty, Sub, discriminate),
    ?assertEqual(
        {fun_full, [ {predef, dynamic} ], {union, [ {var, '$R'}, {predef, dynamic} ]}},
        R
    ).


%% replace_dynamic/1 tests

replace_dynamic_simple_test() ->
    gradual_utils:clean(),
    gradual_utils:init(),
    R = gradual_utils:replace_dynamic({predef, dynamic}),
    ?assertMatch({var, _}, R),
    {var, Name} = R,
    %% frame variable names start with "%"
    ?assertNotEqual(nomatch, string:prefix(atom_to_list(Name), "%")).

replace_dynamic_var_passthrough_test() ->
    gradual_utils:clean(),
    gradual_utils:init(),
    Ty = {var, '$A'},
    ?assertEqual(Ty, gradual_utils:replace_dynamic(Ty)).

replace_dynamic_union_test() ->
    gradual_utils:clean(),
    gradual_utils:init(),
    Ty = {union, [ {predef, dynamic}, {var, '$B'} ]},
    R = gradual_utils:replace_dynamic(Ty),
    ?assertMatch({union, [ {var, _}, {var, '$B'} ]}, R),
    {union, [ {var, Name}, {var, '$B'} ]} = R,
    ?assertNotEqual(nomatch, string:prefix(atom_to_list(Name), "%")).

replace_dynamic_intersection_distinct_test() ->
    gradual_utils:clean(),
    gradual_utils:init(),
    Ty = {intersection, [ {predef, dynamic}, {predef, dynamic} ]},
    R = gradual_utils:replace_dynamic(Ty),
    ?assertMatch({intersection, [ {var, _}, {var, _} ]}, R),
    {intersection, [ {var, N1}, {var, N2} ]} = R,
    ?assertNotEqual(nomatch, string:prefix(atom_to_list(N1), "%")),
    ?assertNotEqual(nomatch, string:prefix(atom_to_list(N2), "%")),
    %% Expect distinct fresh frame vars
    ?assertNotEqual(N1, N2).

replace_dynamic_fun_full_test() ->
    gradual_utils:clean(),
    gradual_utils:init(),
    Ty = {fun_full, [ {predef, dynamic}, {var, '$X'} ], {union, [ {predef, dynamic}, {var, '$Y'} ]}},
    R = gradual_utils:replace_dynamic(Ty),
    ?assertMatch(
        {fun_full, [ {var, _}, {var, '$X'} ], {union, [ {var, _}, {var, '$Y'} ]}},
        R
    ),
    {fun_full, [ {var, A1}, {var, '$X'} ], {union, [ {var, R1}, {var, '$Y'} ]}} = R,
    ?assertNotEqual(nomatch, string:prefix(atom_to_list(A1), "%")),
    ?assertNotEqual(nomatch, string:prefix(atom_to_list(R1), "%")),
    %% Fresh names should differ for different occurrences
    ?assertNotEqual(A1, R1).

replace_dynamic_list_test() ->
    gradual_utils:clean(),
    gradual_utils:init(),
    Ty = {list, {predef, dynamic}},
    R = gradual_utils:replace_dynamic(Ty),
    ?assertMatch({list, {var, _}}, R),
    {list, {var, Name}} = R,
    ?assertNotEqual(nomatch, string:prefix(atom_to_list(Name), "%")).

replace_dynamic_non_dynamic_passthrough_test() ->
    gradual_utils:clean(),
    gradual_utils:init(),
    Ty = {predef, integer},
    ?assertEqual(Ty, gradual_utils:replace_dynamic(Ty)).

