-type opts_mode() :: prod_mode | test_mode.

-record(opts, {log_level = default :: log:log_level() | default,
               help = false :: boolean(),
               dump_raw = false :: boolean(),
               dump = false :: boolean(),
               sanity = false :: boolean(),
               force = false :: boolean(),
               no_type_checking = false :: boolean(),
               no_deps = false :: boolean(),
               check_exports = false :: boolean(),
               type_check_only = [] :: [string()],
               type_check_ignore = [] :: [string()],
               ast_file = empty :: empty | string(),
               project_root = empty :: empty | string(),
               espresso_root = empty :: empty | string(),
               src_paths = [] :: [string()],
               includes = [] :: [string()],
               defines = [] :: [{atom(), string()}],
               load_start = [] :: [string()],
               load_end = [] :: [string()],
               files = [] :: [string()],
               type_overlay = [] :: string(),
               mode = prod_mode :: opts_mode() % only used internally

            }).

-type cmd_opts() :: #opts{}.
