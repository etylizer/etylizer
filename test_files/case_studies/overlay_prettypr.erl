-module(overlay_prettypr).
-compile([export_all, nowarn_export_all]).

% Specs for the functions of prettypr.erl that have none upstream.

% The string of a text: [Width | Chars], string/1 builds it; upstream: #text.s :: deep_string().
-type str() :: [char() | prettypr:deep_string(), ...].
-type doc() :: prettypr:document().

-spec 'prettypr:mktext'(str()) -> {text, str()}.
'prettypr:mktext'(_) -> error(overlay).
-spec 'prettypr:mksep'([doc()], integer(), boolean()) -> {sep, [doc()], integer(), boolean()}.
'prettypr:mksep'(_, _, _) -> error(overlay).
-spec 'prettypr:layout'(doc()) -> string().
'prettypr:layout'(_) -> error(overlay).
-spec 'prettypr:layout'(integer(), doc(), string()) -> string().
'prettypr:layout'(_, _, _) -> error(overlay).
-spec 'prettypr:indent'(integer(), string()) -> string().
'prettypr:indent'(_, _) -> error(overlay).
-spec 'prettypr:flatrev'(prettypr:deep_string(), string()) -> string().
'prettypr:flatrev'(_, _) -> error(overlay).
-spec 'prettypr:flatrev'(prettypr:deep_string(), string(), [prettypr:deep_string()]) -> string().
'prettypr:flatrev'(_, _, _) -> error(overlay).
-spec 'prettypr:rewrite'(doc(), prettypr:ctxt()) -> doc().
'prettypr:rewrite'(_, _) -> error(overlay).
-spec 'prettypr:nil'() -> doc().
'prettypr:nil'() -> error(overlay).
-spec 'prettypr:hspace'() -> doc().
'prettypr:hspace'() -> error(overlay).
-spec 'prettypr:union'(doc(), doc()) -> doc().
'prettypr:union'(_, _) -> error(overlay).
-spec 'prettypr:fit'(doc()) -> doc().
'prettypr:fit'(_) -> error(overlay).
-spec 'prettypr:enter_sep'([doc(), ...], integer(), boolean(), prettypr:ctxt()) -> doc().
'prettypr:enter_sep'(_, _, _, _) -> error(overlay).
-spec 'prettypr:expand_sep'(doc(), [doc()], integer()) -> doc().
'prettypr:expand_sep'(_, _, _) -> error(overlay).
-spec 'prettypr:expand_par'(doc(), [doc(), ...], integer()) -> doc().
'prettypr:expand_par'(_, _, _) -> error(overlay).
-spec 'prettypr:horizontal'([doc(), ...]) -> doc().
'prettypr:horizontal'(_) -> error(overlay).
-spec 'prettypr:vertical'([doc(), ...]) -> doc().
'prettypr:vertical'(_) -> error(overlay).
-spec 'prettypr:foldr1'(fun((T, T) -> T), [T, ...]) -> T.
'prettypr:foldr1'(_, _) -> error(overlay).
-spec 'prettypr:string'(string()) -> str().
'prettypr:string'(_) -> error(overlay).
-spec 'prettypr:concat'(str(), str()) -> str().
'prettypr:concat'(_, _) -> error(overlay).
-spec 'prettypr:string_chars'(str()) -> prettypr:deep_string().
'prettypr:string_chars'(_) -> error(overlay).
-spec 'prettypr:width'(str()) -> non_neg_integer().
'prettypr:width'(_) -> error(overlay).
-spec 'prettypr:is_empty_string'(str()) -> boolean().
'prettypr:is_empty_string'(_) -> error(overlay).
-spec 'prettypr:strwidth'(string()) -> non_neg_integer().
'prettypr:strwidth'(_) -> error(overlay).
-spec 'prettypr:strwidth'(string(), non_neg_integer()) -> non_neg_integer().
'prettypr:strwidth'(_, _) -> error(overlay).
