-module(overlay_erl_anno).
-compile([export_all, nowarn_export_all]).

% Specs for the functions of erl_anno.erl that have none upstream.

-type annos() :: [erl_anno:annotation()].

-spec 'erl_anno:new_location'(erl_anno:location()) -> erl_anno:anno().
'erl_anno:new_location'(_) -> error(overlay).
-spec 'erl_anno:is_anno1'(term()) -> boolean().
'erl_anno:is_anno1'(_) -> error(overlay).
-spec 'erl_anno:is_anno2'(term(), term()) -> boolean().
'erl_anno:is_anno2'(_, _) -> error(overlay).
-spec 'erl_anno:is_filename'(term()) -> boolean().
'erl_anno:is_filename'(_) -> error(overlay).
-spec 'erl_anno:is_string'(term()) -> boolean().
'erl_anno:is_string'(_) -> error(overlay).
-spec 'erl_anno:set'(file | generated | location | end_location | record | text, term(), erl_anno:anno()) -> erl_anno:anno().
'erl_anno:set'(_, _, _) -> error(overlay).
-spec 'erl_anno:set_anno'(file | generated | location | end_location | record | text, term(), annos()) -> erl_anno:anno().
'erl_anno:set_anno'(_, _, _) -> error(overlay).
-spec 'erl_anno:reset'(annos(), atom()) -> erl_anno:anno().
'erl_anno:reset'(_, _) -> error(overlay).
-spec 'erl_anno:reset_simplify'(annos()) -> erl_anno:anno().
'erl_anno:reset_simplify'(_) -> error(overlay).
-spec 'erl_anno:simplify'(annos()) -> erl_anno:anno().
'erl_anno:simplify'(_) -> error(overlay).
-spec 'erl_anno:anno_info'(annos(), generated, false) -> erl_anno:generated();
                          (annos(), record, false) -> erl_anno:record_local();
                          (annos(), location, 0) -> erl_anno:location().
'erl_anno:anno_info'(_, _, _) -> error(overlay).
-spec 'erl_anno:anno_info'(annos(), file) -> erl_anno:filename() | undefined;
                          (annos(), text) -> erl_anno:text() | undefined;
                          (annos(), end_location) -> erl_anno:location() | undefined;
                          (annos(), atom()) -> term().
'erl_anno:anno_info'(_, _) -> error(overlay).
-spec 'erl_anno:end_location'(string(), erl_anno:line(), erl_anno:column()) -> erl_anno:location().
'erl_anno:end_location'(_, _, _) -> error(overlay).
-spec 'erl_anno:end_location'(string(), erl_anno:line()) -> erl_anno:line().
'erl_anno:end_location'(_, _) -> error(overlay).
-spec 'erl_anno:is_settable'(atom(), term()) -> boolean().
'erl_anno:is_settable'(_, _) -> error(overlay).
-spec 'erl_anno:default'(atom(), term()) -> boolean().
'erl_anno:default'(_, _) -> error(overlay).
