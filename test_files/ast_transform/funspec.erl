-module(funspec).

-compile(export_all).
-compile(nowarn_export_all).

% Erlang restricts the scope of a type variable to one branch of the intersection.
% However, we quantify the outermost level (it's more flexible because it allows
% sharing of type variables between branches of the intersection).
% In the example below, using X and not _X does not work, because X would then
% appear only once in the second branch and Erlang does not like that.
-spec foo({_X, integer()}) -> _X when _X :: atom()
         ; ({_X, [Y]}) -> Y when Y :: number().
foo(_) -> ok.
