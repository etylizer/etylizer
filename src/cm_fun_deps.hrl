-record(fun_info, {
    body_hash :: string(),
    spec_hash :: string() | no_spec,
    calls :: [cm_fun_deps:fun_id()]
}).

-record(module_info, {
    decls_hash :: string(), % forms w/o funs and specs
    funs :: #{ast:fun_with_arity() => #fun_info{}}
}).
