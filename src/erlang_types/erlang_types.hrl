-type type_descriptor() :: dnf_ty_variable:type().
-type variable() :: ty_variable:type().
-type monomorphic_variables() :: etally:monomorphic_variables().

-type is_empty_cache() :: #{type_descriptor() => boolean()}.
% like is_empty_cache(), by the descriptor that a node is loaded to
-type normalize_cache() :: #{{type_descriptor(), monomorphic_variables()} => constraint_set:set_of_constraint_sets()}.
-type unparse_cache() :: #{ty_node:type() => ast_ty()}.

-type ast_ty() :: ast:ty().
-type ast_mu_var() :: ast:ty_mu_var().
