-type type_descriptor() :: dnf_ty_variable:type().
-type variable() :: ty_variable:type().
-type monomorphic_variables() :: etally:monomorphic_variables().

-type is_empty_cache() :: #{type_descriptor() => boolean()}.
-type normalize_cache() :: #{
    {ty_node:type(), monomorphic_variables()} => constraint_set:set_of_constraint_sets(),
    %% dnf_ty_tuple:phi_norm/4 stashes a sub-problem memo in the same threaded
    %% map, keyed by its (BigS, NegList) pair under a distinguishing tag.
    {phi_norm_tuple_memo, [ty_node:type()], [ty_tuple:type()]} => constraint_set:set_of_constraint_sets()
}.
-type all_variables_cache() :: #{ty_node:type() => _}.
-type unparse_cache() :: #{ty_node:type() => ast_ty()}.

-type ast_ty() :: ast:ty().
-type ast_mu_var() :: ast:ty_mu_var().
