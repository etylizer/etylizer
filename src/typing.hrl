-record(ctx,
        { symtab :: symtab:t(),
          overlay_symtab :: symtab:t(),
          sanity :: t:opt(ast_check:ty_map()),
          gradual_typing_mode = infer :: infer | dynamic,
          report_mode :: feature_flags:report_mode(),
          report_timeout :: pos_integer(),
          exhaustiveness_mode :: feature_flags:exhaustiveness_mode()
        }).

-type ctx() :: #ctx{}.
