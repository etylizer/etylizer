-module(cm_index).

% @doc This module maintains an index of files together with their hashes to enable
% the detection of changes in the content or the exported interface of the
% corresponding module, down to its functions.

-export([
    load_index/3,
    save_index/2,
    has_file_changed/2,
    has_exported_interface_changed/3,
    has_external_dep_changed/3,
    changed_functions/3,
    callers/2,
    needs_recheck/2,
    insert/5
]).

-export_type([index/0, failure/0]).

-include("log.hrl").
-include("etylizer_main.hrl").
-include("etylizer.hrl").
-include("cm_fun_deps.hrl").

-type failure() :: error | timeout.

-type file_entry() ::
    {[{file:filename(), string() | {error, any()}}], string(),
     cm_fun_deps:module_info(), [{ast:fun_with_arity(), failure()}]}.

-type index() :: {
    % OTP version, hash of rebar.lock, stamp of the options and the checker
    {string(), string(), term()},
    % map .erl-file -> file_entry()
    #{file:filename() => file_entry()}
    }.

% Format of index on disk:
%-type stored_index() :: {
%    etylizer_index,
%    integer(), % version
%    index()
%}.

-define(INDEX_VERSION, 5).

-spec empty_index(file:filename(), term()) -> index().
empty_index(RebarLockFile, Stamp) ->
    Deps = get_external_deps(RebarLockFile, Stamp),
    {Deps, maps:new()}.

% replace index that cannot be used
-spec load_index(file:filename(), term(), file:filename()) -> index().
load_index(RebarLockFile, Stamp, Path) ->
    BadIndex =
        fun(Msg) ->
            ?LOG_WARN(Msg),
            empty_index(RebarLockFile, Stamp)
        end,
    case filelib:is_file(Path) of
        true ->
            case file:consult(Path) of
                {ok, [{etylizer_index, ?INDEX_VERSION, Index}]} ->
                    ?LOG_TRACE("Loading index from ~p", Path),
                    ?assert_type(Index, index());
                {ok, []} ->
                    BadIndex(utils:sformat("Empty index at ~p", Path));
                {ok, _} ->
                    BadIndex(utils:sformat("Index with unexpected content at ~p", Path));
                {error, Reason} ->
                    BadIndex(utils:sformat(
                        "Error occurred while trying to load existing index. Reason: ~200p",
                        Reason))
            end;
        false ->
            ?LOG_DEBUG("No index exists at ~p, using empty index", Path),
            empty_index(RebarLockFile, Stamp)
    end.

-spec save_index(file:filename(), index()) -> ok.
save_index(Path, Index) ->
    filelib:ensure_dir(Path),
    Formatted = lists:flatten(io_lib:format("~p.~n", [{etylizer_index, ?INDEX_VERSION, Index}])),
    case file:write_file(Path, ?assert_type(Formatted, string())) of
        ok -> ok;
        Error -> ?ABORT("Could not save the index at ~p: ~p", Path, Error)
    end.

% Whether the file or one of the headers it includes changed.
-spec has_file_changed(file:filename(), index()) -> boolean().
has_file_changed(Path, {_, Index}) ->
    case maps:find(Path, Index) of
        {ok, {Sources, _, _, _}} ->
            lists:any(fun({File, Hash}) -> utils:hash_file(File) =/= Hash end, Sources);
        error -> true
    end.

-spec needs_recheck(file:filename(), index()) -> [ast:fun_with_arity()].
needs_recheck(Path, {_, Index}) ->
    case maps:find(Path, Index) of
        {ok, {_, _, _, Failed}} -> [F || {F, _} <- Failed];
        error -> []
    end.

-spec has_exported_interface_changed(file:filename(), ast:forms(), index()) -> boolean().
has_exported_interface_changed(Path, Forms, {_, Index}) ->
    case maps:find(Path, Index) of
        {ok, {_, InterfaceHash, _, _}} -> interface_hash(Forms) =/= InterfaceHash;
        error -> true
    end.

-spec interface_hash(ast:forms()) -> string().
interface_hash(Forms) ->
    Interface = cm_module_interface:extract_interface_declaration(Forms),
    utils:hash_sha1(?assert_type(io_lib:write(Interface), iodata())).

-spec analyze(file:filename(), ast:forms()) -> cm_fun_deps:module_info().
analyze(Path, Forms) ->
    cm_fun_deps:analyze_module(ast_utils:modname_from_path(Path), Forms).

% The functions of a file whose content asks for a recheck: all of them if the file is
% new or its declarations changed, otherwise the new and the changed ones. And the
% functions whose callers have to be rechecked: those with a new or changed spec and
% those that are gone.
-spec changed_functions(file:filename(), ast:forms(), index()) ->
    {all | [ast:fun_with_arity()], [ast:fun_with_arity()]}.
changed_functions(Path, Forms, {_, Index}) ->
    #module_info{decls_hash = DeclsHash, funs = Funs} = analyze(Path, Forms),
    case maps:find(Path, Index) of
        {ok, {_, _, #module_info{decls_hash = OldDeclsHash, funs = OldFuns}, _}} ->
            New = maps:to_list(Funs),
            Changed =
                case OldDeclsHash =:= DeclsHash of
                    true -> [F || {F, Info} <- New, maps:find(F, OldFuns) =/= {ok, Info}];
                    false -> all
                end,
            SpecChanged = [F || {F, #fun_info{spec_hash = SpecHash}} <- New,
                                old_spec_hash(F, OldFuns) =/= SpecHash],
            Gone = [F || F <- maps:keys(OldFuns), not maps:is_key(F, Funs)],
            {Changed, SpecChanged ++ Gone};
        error ->
            {all, []}
    end.

-spec old_spec_hash(ast:fun_with_arity(), #{ast:fun_with_arity() => cm_fun_deps:fun_info()}) ->
    string() | no_spec | new.
old_spec_hash(Fun, OldFuns) ->
    case maps:find(Fun, OldFuns) of
        {ok, #fun_info{spec_hash = SpecHash}} -> SpecHash;
        error -> new
    end.

% The functions calling one of the given functions, by file
-spec callers([cm_fun_deps:fun_id()], index()) -> [{file:filename(), [ast:fun_with_arity()]}].
callers([], _) -> [];
callers(Callees, {_, Index}) ->
    lists:filtermap(
        fun({Path, {_, _, #module_info{funs = Funs}, _}}) ->
            Callers = [F || {F, #fun_info{calls = Calls}} <- maps:to_list(Funs),
                            lists:any(fun(C) -> lists:member(C, Callees) end, Calls)],
            Callers =/= [] andalso {true, {Path, Callers}}
        end, maps:to_list(Index)).

-spec get_external_deps(file:filename(), term()) -> {string(), string(), term()}.
get_external_deps(RebarLockFile, Stamp) ->
    OtpVersion = erlang:system_info(otp_release),
    RebarHash =
        case utils:hash_file(RebarLockFile) of
            {error, _} ->
                case filelib:is_file(paths:rebar_config_from_lock_file(RebarLockFile)) of
                    true ->
                        ?ABORT("Could not read rebar's lock file at ~p. Please build your project " ++
                                "with rebar before using etylizer.", RebarLockFile);
                    false ->
                        []
                end;
            H -> H
        end,
    {OtpVersion, RebarHash, Stamp}.

-spec has_external_dep_changed(file:filename(), term(), index()) -> {boolean(), index()}.
has_external_dep_changed(RebarLockFile, Stamp, {{StoredOtpVersion, StoredRebarHash, StoredStamp}, Index}) ->
    New = {OtpVersion, RebarHash, _} = get_external_deps(RebarLockFile, Stamp),
    Changed =
        case {OtpVersion =:= StoredOtpVersion, RebarHash =:= StoredRebarHash, Stamp =:= StoredStamp} of
            {true, true, true} -> false;
            {false, _, _} ->
                ?LOG_INFO("OTP version changed from ~p to ~p", StoredOtpVersion, OtpVersion),
                true;
            {true, false, _} ->
                ?LOG_INFO("Rebar lock file ~p changed", RebarLockFile),
                true;
            {true, true, false} ->
                ?LOG_INFO("The options or the checker changed"),
                true
        end,
    case Changed of
        true -> {true, {New, #{}}};
        false -> {false, {New, Index}}
    end.

% Failed are the functions that got no ok verdict.
-spec insert(file:filename(), ast:forms(), [file:filename()],
    [{ast:fun_with_arity(), failure()}], index()) -> index().
insert(Path, Forms, Headers, Failed, {DepVersions, Index}) ->
    Sources = [{File, utils:hash_file(File)} || File <- [Path | Headers]],
    Entry = {Sources, interface_hash(Forms), analyze(Path, Forms), Failed},
    {DepVersions, maps:put(Path, Entry, Index)}.
