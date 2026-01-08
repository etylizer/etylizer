-module(type_annotation).

-compile(export_all).
-compile(nowarn_export_all).

-include("etylizer.hrl").

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

%%%%%%%%%%%%%%%%%%%%%%%% TYPE ANNOTATIONS    %%%%%%%%%%%%%%%%%%%%%%%%
 
% user-defined type
-spec annot_01() -> atom().
annot_01() -> ?annotate_type(foobar, atom()).

