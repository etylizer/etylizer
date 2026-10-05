-module(external_types).

% @doc Types that are not part of a data model. They are artefacts of type checking:
% they only exist because etylizer needs them to check a function, for example as the
% type of everything a generic traversal can come across.

-export_type([
    subterm/0
]).

%% ---------------------------------------------------------------------------
%% Internal AST (ast.erl)
%% ---------------------------------------------------------------------------

% Everything that forms consist of: lists, the tuples of the AST, and the atoms and
% numbers inside of them. Guard tests are covered by ast:exp(). The options of compile
% attributes are arbitrary terms and not included.
%
% The type is closed: every list element and every tuple component of a subterm is a
% subterm again. This is what generic traversals of the AST need, and etylizer proves it
% when it checks ast_traverse:subterms/1. A new kind of tuple in the AST has to be added
% here, otherwise that function no longer type checks.
-type subterm() ::
      [subterm()]
      % forms
    | ast:form() | ast:fun_with_arity() | {atom(), [ast:fun_with_arity()] | [ast:record_field()]}
    | ast:record_field() | ast:tydef() | ast:ty_scheme() | ast:bounded_tyvar() | ast:etylizer_opt()
      % clauses, expressions and patterns
    | ast:case_clause() | ast:catch_clause()
    | ast:exp() | ast:pat() | ast:generators() | ast:map_assoc() | ast:pat_map_assoc()
    | ast:exp_bitstring_elem() | ast:pat_bitstring_elem() | ast:bitstring_tyspec()
    | ast:any_ref() | ast:local_bind() | ast:local_varname() | ast:global_ref_dyn()
      % types
    | ast:ty() | ast:ty_map_assoc() | ast:ty_ref()
      % leaves
    | ast:loc() | atom() | number().
