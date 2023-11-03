-module('grad-405_list').

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eunit/include/eunit.hrl").

% https://github.com/josefs/Gradualizer/issues/405

-spec i([atom()]) -> ok.
i([]) -> ok;
i([_Cs]) -> ok;
i([_C1, _C2 | _Cs]) -> ok.
