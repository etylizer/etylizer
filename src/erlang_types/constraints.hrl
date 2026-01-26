-type set_of_constraint_sets() :: set_of_constraint_sets_rep().
-type set_of_constraint_sets_rep() :: [constraint_set()].

-type constraint_set() :: [constraint()].
-type constraint() :: {ty_variable:type(), ty:type(), ty:type()}.
-type variable() :: ty_variable:type().

-type monomorphic_variables() :: #{variable() => _}.
