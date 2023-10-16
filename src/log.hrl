-ifndef(LOG_HRL).
-define(LOG_HRL,true).

-define(ABORT(A),?DO_LOG_AND_DIE(abort,[A])).
-define(ABORT(A,B),?DO_LOG_AND_DIE(abort,[A,B])).
-define(ABORT(A,B,C),?DO_LOG_AND_DIE(abort,[A,B,C])).
-define(ABORT(A,B,C,D),?DO_LOG_AND_DIE(abort,[A,B,C,D])).
-define(ABORT(A,B,C,D,E),?DO_LOG_AND_DIE(abort,[A,B,C,D,E])).

-define(LOG_ERROR(A),?DO_LOG(error,[A])).
-define(LOG_ERROR(A,B),?DO_LOG(error,[A,B])).
-define(LOG_ERROR(A,B,C),?DO_LOG(error,[A,B,C])).
-define(LOG_ERROR(A,B,C,D),?DO_LOG(error,[A,B,C,D])).
-define(LOG_ERROR(A,B,C,D,E),?DO_LOG(error,[A,B,C,D,E])).

-define(LOG_WARN(A),?DO_LOG(warn,[A])).
-define(LOG_WARN(A,B),?DO_LOG(warn,[A,B])).
-define(LOG_WARN(A,B,C),?DO_LOG(warn,[A,B,C])).
-define(LOG_WARN(A,B,C,D),?DO_LOG(warn,[A,B,C,D])).
-define(LOG_WARN(A,B,C,D,E),?DO_LOG(warn,[A,B,C,D,E])).
-define(LOG_WARN(A,B,C,D,E,F),?DO_LOG(warn,[A,B,C,D,E,F])).
-define(LOG_WARN(A,B,C,D,E,F,G),?DO_LOG(warn,[A,B,C,D,E,F,G])).
-define(LOG_WARN(A,B,C,D,E,F,G,H),?DO_LOG(warn,[A,B,C,D,E,F,G,H])).
-define(LOG_WARN(A,B,C,D,E,F,G,H,I),?DO_LOG(warn,[A,B,C,D,E,F,G,H,I])).
-define(LOG_WARN(A,B,C,D,E,F,G,H,I,J),?DO_LOG(warn,[A,B,C,D,E,F,G,H,I,J])).
-define(LOG_WARN(A,B,C,D,E,F,G,H,I,J,K),?DO_LOG(warn,[A,B,C,D,E,F,G,H,I,J,K])).
-define(LOG_WARN(A,B,C,D,E,F,G,H,I,J,K,L),?DO_LOG(warn,[A,B,C,D,E,F,G,H,I,J,K,L])).
-define(LOG_WARN(A,B,C,D,E,F,G,H,I,J,K,L,M),?DO_LOG(warn,[A,B,C,D,E,F,G,H,I,J,K,L,M])).
-define(LOG_WARN(A,B,C,D,E,F,G,H,I,J,K,L,M,N),?DO_LOG(warn,[A,B,C,D,E,F,G,H,I,J,K,L,M,N])).

-define(LOG_NOTE(A),?DO_LOG(note,[A])).
-define(LOG_NOTE(A,B),?DO_LOG(note,[A,B])).
-define(LOG_NOTE(A,B,C),?DO_LOG(note,[A,B,C])).
-define(LOG_NOTE(A,B,C,D),?DO_LOG(note,[A,B,C,D])).
-define(LOG_NOTE(A,B,C,D,E),?DO_LOG(note,[A,B,C,D,E])).
-define(LOG_NOTE(A,B,C,D,E,F),?DO_LOG(NOTE,[A,B,C,D,E,F])).
-define(LOG_NOTE(A,B,C,D,E,F,G),?DO_LOG(NOTE,[A,B,C,D,E,F,G])).
-define(LOG_NOTE(A,B,C,D,E,F,G,H),?DO_LOG(note,[A,B,C,D,E,F,G,H])).
-define(LOG_NOTE(A,B,C,D,E,F,G,H,I),?DO_LOG(note,[A,B,C,D,E,F,G,H,I])).
-define(LOG_NOTE(A,B,C,D,E,F,G,H,I,J),?DO_LOG(note,[A,B,C,D,E,F,G,H,I,J])).
-define(LOG_NOTE(A,B,C,D,E,F,G,H,I,J,K),?DO_LOG(note,[A,B,C,D,E,F,G,H,I,J,K])).
-define(LOG_NOTE(A,B,C,D,E,F,G,H,I,J,K,L),?DO_LOG(note,[A,B,C,D,E,F,G,H,I,J,K,L])).
-define(LOG_NOTE(A,B,C,D,E,F,G,H,I,J,K,L,M),?DO_LOG(note,[A,B,C,D,E,F,G,H,I,J,K,L,M])).
-define(LOG_NOTE(A,B,C,D,E,F,G,H,I,J,K,L,M,N),?DO_LOG(note,[A,B,C,D,E,F,G,H,I,J,K,L,M,N])).

-define(LOG_INFO(A),?DO_LOG(info,[A])).
-define(LOG_INFO(A,B),?DO_LOG(info,[A,B])).
-define(LOG_INFO(A,B,C),?DO_LOG(info,[A,B,C])).
-define(LOG_INFO(A,B,C,D),?DO_LOG(info,[A,B,C,D])).
-define(LOG_INFO(A,B,C,D,E),?DO_LOG(info,[A,B,C,D,E])).
-define(LOG_INFO(A,B,C,D,E,F),?DO_LOG(info,[A,B,C,D,E,F])).
-define(LOG_INFO(A,B,C,D,E,F,G),?DO_LOG(info,[A,B,C,D,E,F,G])).
-define(LOG_INFO(A,B,C,D,E,F,G,H),?DO_LOG(info,[A,B,C,D,E,F,G,H])).
-define(LOG_INFO(A,B,C,D,E,F,G,H,I),?DO_LOG(info,[A,B,C,D,E,F,G,H,I])).
-define(LOG_INFO(A,B,C,D,E,F,G,H,I,J),?DO_LOG(info,[A,B,C,D,E,F,G,H,I,J])).
-define(LOG_INFO(A,B,C,D,E,F,G,H,I,J,K),?DO_LOG(info,[A,B,C,D,E,F,G,H,I,J,K])).
-define(LOG_INFO(A,B,C,D,E,F,G,H,I,J,K,L),?DO_LOG(info,[A,B,C,D,E,F,G,H,I,J,K,L])).
-define(LOG_INFO(A,B,C,D,E,F,G,H,I,J,K,L,M),?DO_LOG(info,[A,B,C,D,E,F,G,H,I,J,K,L,M])).
-define(LOG_INFO(A,B,C,D,E,F,G,H,I,J,K,L,M,N),?DO_LOG(info,[A,B,C,D,E,F,G,H,I,J,K,L,M,N])).

-define(LOG_DEBUG(A),?DO_LOG(debug,[A])).
-define(LOG_DEBUG(A,B),?DO_LOG(debug,[A,B])).
-define(LOG_DEBUG(A,B,C),?DO_LOG(debug,[A,B,C])).
-define(LOG_DEBUG(A,B,C,D),?DO_LOG(debug,[A,B,C,D])).
-define(LOG_DEBUG(A,B,C,D,E),?DO_LOG(debug,[A,B,C,D,E])).
-define(LOG_DEBUG(A,B,C,D,E,F),?DO_LOG(debug,[A,B,C,D,E,F])).
-define(LOG_DEBUG(A,B,C,D,E,F,G),?DO_LOG(debug,[A,B,C,D,E,F,G])).
-define(LOG_DEBUG(A,B,C,D,E,F,G,H),?DO_LOG(debug,[A,B,C,D,E,F,G,H])).
-define(LOG_DEBUG(A,B,C,D,E,F,G,H,I),?DO_LOG(debug,[A,B,C,D,E,F,G,H,I])).
-define(LOG_DEBUG(A,B,C,D,E,F,G,H,I,J),?DO_LOG(debug,[A,B,C,D,E,F,G,H,I,J])).
-define(LOG_DEBUG(A,B,C,D,E,F,G,H,I,J,K),?DO_LOG(debug,[A,B,C,D,E,F,G,H,I,J,K])).
-define(LOG_DEBUG(A,B,C,D,E,F,G,H,I,J,K,L),?DO_LOG(debug,[A,B,C,D,E,F,G,H,I,J,K,L])).
-define(LOG_DEBUG(A,B,C,D,E,F,G,H,I,J,K,L,M),?DO_LOG(debug,[A,B,C,D,E,F,G,H,I,J,K,L,M])).
-define(LOG_DEBUG(A,B,C,D,E,F,G,H,I,J,K,L,M,N),?DO_LOG(debug,[A,B,C,D,E,F,G,H,I,J,K,L,M,N])).

-define(LOG_TRACE(A),?DO_LOG(trace,[A])).
-define(LOG_TRACE(A,B),?DO_LOG(trace,[A,B])).
-define(LOG_TRACE(A,B,C),?DO_LOG(trace,[A,B,C])).
-define(LOG_TRACE(A,B,C,D),?DO_LOG(trace,[A,B,C,D])).
-define(LOG_TRACE(A,B,C,D,E),?DO_LOG(trace,[A,B,C,D,E])).
-define(LOG_TRACE(A,B,C,D,E,F),?DO_LOG(trace,[A,B,C,D,E,F])).
-define(LOG_TRACE(A,B,C,D,E,F,G),?DO_LOG(trace,[A,B,C,D,E,F,G])).
-define(LOG_TRACE(A,B,C,D,E,F,G,H),?DO_LOG(trace,[A,B,C,D,E,F,G,H])).
-define(LOG_TRACE(A,B,C,D,E,F,G,H,I),?DO_LOG(trace,[A,B,C,D,E,F,G,H,I])).
-define(LOG_TRACE(A,B,C,D,E,F,G,H,I,J),?DO_LOG(trace,[A,B,C,D,E,F,G,H,I,J])).
-define(LOG_TRACE(A,B,C,D,E,F,G,H,I,J,K),?DO_LOG(trace,[A,B,C,D,E,F,G,H,I,J,K])).
-define(LOG_TRACE(A,B,C,D,E,F,G,H,I,J,K,L),?DO_LOG(trace,[A,B,C,D,E,F,G,H,I,J,K,L])).
-define(LOG_TRACE(A,B,C,D,E,F,G,H,I,J,K,L,M),?DO_LOG(trace,[A,B,C,D,E,F,G,H,I,J,K,L,M])).
-define(LOG_TRACE(A,B,C,D,E,F,G,H,I,J,K,L,M,N),?DO_LOG(trace,[A,B,C,D,E,F,G,H,I,J,K,L,M,N])).

%%%-----------------------------------------------------------------
%%% Internal, i.e. not intended for direct use in code - use above
%%% macros instead!
-define(DO_LOG(Level,Args),
        case log:allow(Level) of
            true ->
                log:macro_log(?FILE, ?LINE, Level, hd(Args), tl(Args));
            false ->
                ok
        end).
-define(DO_LOG_AND_DIE(Level,Args),
    log:macro_log(?FILE, ?LINE, Level, "Aborting: " ++ hd(Args), tl(Args)),
    throw({ety, abort, "Aborting"})
).
-endif.
