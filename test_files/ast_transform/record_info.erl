-module(record_info).

-compile(export_all).
-compile([nowarn_export_all, nowarn_shadow_vars]).

-record(parse_opts,
    {
        includes = [] :: [string()],
        defines = [] :: [{atom(), string()}],
        verbose = true :: boolean()
    }).

foo() -> record_info(fields, parse_opts).
