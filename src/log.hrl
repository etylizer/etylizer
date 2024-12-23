-ifndef(LOG_HRL).
-define(LOG_HRL,true).

-define(ABORT(A),?DO_LOG_AND_DIE(abort,A,[])).
-define(ABORT(A,B),?DO_LOG_AND_DIE(abort,A,[B])).
-define(ABORT(A,B,C),?DO_LOG_AND_DIE(abort,A,[B,C])).
-define(ABORT(A,B,C,D),?DO_LOG_AND_DIE(abort,A,[B,C,D])).
-define(ABORT(A,B,C,D,E),?DO_LOG_AND_DIE(abort,A,[B,C,D,E])).

%%%-----------------------------------------------------------------
%%% Internal, i.e. not intended for direct use in code - use above
%%% macros instead!
-define(DO_LOG_AND_DIE(Level,A0,Args),
    logger:Level("Aborting: " ++ A0, Args),
    throw({ety, abort, "Aborting"})
).
-endif.
