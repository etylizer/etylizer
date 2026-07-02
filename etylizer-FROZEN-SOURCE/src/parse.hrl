-record(parse_opts,
    {
        includes = [] :: [string()],
        defines = [] :: [{atom(), string()}],
        verbose = false :: boolean()
    }).

-type parse_opts() :: #parse_opts{}.
