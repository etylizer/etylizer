
-record(parse_opts,
    {
        includes = [] :: [string()],
        defines = [] :: [{atom(), string()}],
        verbose = true :: boolean()
    }).

-type parse_opts() :: #parse_opts{}.
