% What incremental type checking needs to know about a function
-record(fun_info, {
    body_hash :: string(),
    spec_hash :: string(), % "" without a spec
    calls :: [cm_fun_deps:fun_id()]
}).

-record(module_info, {
    decls_hash :: string(), % all forms but the functions and their specs
    funs :: #{ast:fun_with_arity() => #fun_info{}}
}).
