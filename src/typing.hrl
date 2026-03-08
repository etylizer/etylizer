-record(ctx,
        { symtab :: symtab:t(),
          overlay_symtab :: symtab:t(),
          sanity :: t:opt(ast_check:ty_map()),
          gradual_typing_mode = dynamic :: feature_flags:gradual_typing_mode(),
          report_mode :: feature_flags:report_mode(),
          report_timeout :: pos_integer(),
          exhaustiveness_mode :: feature_flags:exhaustiveness_mode(),
          % functions where exhaustiveness checking is disabled at the function clause level
          % via -etylizer({functions_exhaustive, off, [...]})
          disable_exhaustiveness = sets:new() :: sets:set({atom(), arity()}),
          % functions where redundancy checking is disabled at the function clause level
          % via -etylizer({functions_redundant, off, [...]})
          disable_redundancy = sets:new() :: sets:set({atom(), arity()})
        }).

-type ctx() :: #ctx{}.
