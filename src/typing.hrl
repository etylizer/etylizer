-record(ctx,
        { symtab :: symtab:t(),
          sanity :: t:opt(ast_check:ty_map())
        }).
-opaque ctx() :: #ctx{}.
