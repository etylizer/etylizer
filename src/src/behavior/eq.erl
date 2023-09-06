-module(eq).
-vsn({2,0,0}).

-type x() :: term().

%% Used to compare types
-callback equal(x(), x()) -> boolean().

%% -1 less, 0 equal, 1 bigger
-callback compare(x(), x()) -> -1 | 0 | 1.

