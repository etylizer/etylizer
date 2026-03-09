-record(person, {name :: string(),
                 age :: integer(),
                 address :: string()}).

-record(item, {value :: integer(),
               label :: string(),
               count = 0 :: integer()}).

-record(config, {host :: string(),
                 port :: string(),
                 path :: string()}).

