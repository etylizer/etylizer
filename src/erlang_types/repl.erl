-module(repl).

-compile([export_all, nowarn_export_all]).

% REPL for the erlang_types library
%
% Supports:
%   multi-line commands separated by ;;
%   persistent history saved at $XDG_CACHE_HOME/etylizer-repl.history navigated via arrows up/down
%   auto-complete commands with tab
%   TODO reverse search history with ^R
%   TODO unicode input?
%
% TODO:
%   * fix type errors
%   * resizing breaks terminal; work around: clear on resize
%   * implement input beyond the column limit (start next line)
%
% Documentation:
%   https://www.erlang.org/doc/apps/stdlib/terminal_interface.html
%   https://www.erlang.org/doc/apps/stdlib/custom_shell.html
%
% Considerations:
%  * cooked mode handles terminal resizing properly, 
%    but can't react to character command sequences immediately (e.g up/down arrow support?)
%  * no documentation on how to use edlin properly
%    * -> supports history, multi-line movement, tab completion
%    * how to make cooked mode history persistent?
%    * cooked can handle most things, but not sure how to use the interface provided
%  * erl shell stops on end of column limit
%

-etylizer({disable_exhaustiveness_toplevel, [color/2]}).

-include("etylizer.hrl").

-type history() :: list(nonempty_list(string())).
-record(state, {
    lines = [""] :: nonempty_list(string()),  % list of lines in current command
    cursor_row = 0 :: non_neg_integer(),  % row index in lines (0-based)
    cursor_col = 0 :: non_neg_integer(),   % column in current line
    history = [] :: history(),  % list of commands, each command is list of lines
    history_index = none :: none | non_neg_integer()
}).
-type state() :: #state{}.

-define(HISTORY_FILE, "etylizer-repl.history"). % saved at $XDG_CACHE_HOME
-define(COMMANDS, ["q", "help", "clear"]).
-define(PRINT_VERSION, io:format("erlang_types REPL v0.0.2-rc\n\r" ++ color("help;;", yellow) ++ " for help\n\r")).


-spec main(_) -> no_return().
main(_) ->
    % initialize erlang_types global state
    global_state:init(),
    % is stdin enabled or not?
    case proplists:get_value(stdin, io:getopts()) of
        true -> % interactive
            shell:start_interactive({noshell, raw}),
            % io:put_chars("\e[?1049h"), % enable alternate screen buffer
            % io:put_chars("\e[2J\e[H"), % clear screen
            io:format("\e[?7l"), % enable line wrap
            History = load_history(),
            State = #state{history = History, lines = [""], cursor_row = 0, history_index = none, cursor_col = 0}, 
            ?PRINT_VERSION,
            update_display(State, State),
            loop(State);
        false -> % non-interactive
            process_input_stream([]);
        _ -> error(non_exhaustive) % FIXME TE mark non-exhaustive fun
    end.

-spec update_display(state(), state()) -> state().
update_display(State, NewState) ->
    #state{lines = Lines, cursor_row = Row} = State,
    % true = length(Lines) > 0,
    % true = Row < length(Lines),
    
    % move cursor up from Row to the beginning of the command
    case Row of % FIXME TE ?
        0 -> ok;
        N -> io:format("\e[~BA", [N])
    end,
    io:format("\r"),
    % clear entire command area by moving down and clearing all lines
    clear_command_area(length(Lines)),
    
    % print all lines from NewState
    #state{lines = NewLines} = NewState,
    lists:foreach(fun({Line, Index}) ->
        Prompt = case Index of
            0 -> "> ";
            _ -> "  "
        end,
        io:format("~s~s\n\r", [Prompt, Line])
    end, lists:zip(NewLines, lists:seq(0, length(NewLines) - 1))),

    % restore initial position and position cursor correctly
    io:format("\e[~BA", [length(NewLines)]),
    update_cursor_pos(NewState),
    NewState.

-spec clear_command_area(pos_integer()) -> _.
clear_command_area(N) ->
    % true = N > 0,
    % clear N lines starting from current position
    lists:foreach(fun(_) ->
        io:format("\e[2K\n\r")
    end, lists:seq(1, N)),
    % move back up to start position
    io:format("\e[~BA", [N]).

-spec update_cursor_pos(state()) -> state().
update_cursor_pos(S = #state{cursor_row = Row, cursor_col = Col}) ->
    case Row > 0 of
      true ->
        % move to row
        io:format("\e[~BB", [Row]);
      _ -> ok
    end,
    % move to correct column
    io:format("\r\e[~BC", [Col + 2]), % + prompt length
    S.


-spec process_input_stream(string()) -> no_return().
process_input_stream(Acc) ->
    case io:get_line('') of
        eof -> halt(0);
        {error, _reason} -> halt(1); % TODO error message why it failed
        Line ->
            CleanLine = ?assert_type(string:trim(Line, trailing, "\n\r"), string()), % TODO unicode
            NewAcc = Acc ++ CleanLine,
            case lists:suffix(";;", NewAcc) of
                true ->
                    handle_command(lists:sublist(NewAcc, length(NewAcc) - 2)), % remove ;;
                    process_input_stream([]);
                false ->
                    process_input_stream(NewAcc)
            end
    end.

-spec loop(state()) -> no_return().
loop(State) ->
    Key = get_key(),
    NewState = handle_key(Key, State),
    loop(NewState).

-spec handle_key([char()], state()) -> state().
handle_key([127], State) -> handle_backspace(State);
handle_key([13], State) -> handle_enter(State);
handle_key([9], State) -> handle_tab(State);
handle_key([27,91,65], State) -> handle_arrow_up(State);
handle_key([27,91,66], State) -> handle_arrow_down(State);
handle_key([27,91,67], State) -> handle_arrow_right(State);
handle_key([27,91,68], State) -> handle_arrow_left(State);
handle_key([27,91,72], State) -> handle_home(State);
handle_key([27,91,70], State) -> handle_end(State);
% handle_key([27,91,51,126], State) -> handle_delete(State);
handle_key([Char], State) when is_integer(Char), Char >= 32, Char =< 126 ->
    handle_printable(Char, State);
handle_key(_, State) ->
    % TODO unicode characters here
    % ignore other special keys
    State.

-spec handle_printable(char(), state()) -> state().
handle_printable(Char, State) ->
    #state{lines = Lines, cursor_row = Row, cursor_col = Col} = State,
    CurrentLine = lists:nth(?assert_type(Row + 1, pos_integer()), Lines), % FIXME TE
    {Before, After} = split_at(CurrentLine, Col),
    NewLine = Before ++ [Char] ++ After,
    NewLines = replace_at(Lines, Row, NewLine),
    update_display(State, State#state{
        lines = NewLines,
        cursor_col = Col + 1
    }).

-spec handle_backspace(state()) -> state().
handle_backspace(State) ->
    #state{lines = Lines, cursor_row = Row, cursor_col = Col} = State,
    case Col > 0 of
        true ->
            CurrentLine = lists:nth(?assert_type(Row + 1, pos_integer()), Lines),
            {Before, After} = split_at(CurrentLine, ?assert_type(Col - 1, non_neg_integer())), % Col > 0
            NewLine = Before ++ tl(?assert_type(After, nonempty_list(string()))), % TODO assert why?
            NewLines = replace_at(Lines, Row, NewLine),
            update_display(State, State#state{
                lines = NewLines,
                cursor_col = ?assert_type(Col - 1, non_neg_integer())
            });
        false when Row > 0 ->
            % remove line
            NewLines = ?assert_type(lists:reverse(tl(lists:reverse(Lines))), nonempty_list(string())), % FIXME TE
            CurrentLine = lists:nth(?assert_type(Row, pos_integer()), NewLines),
            update_display(State, State#state{lines = NewLines, cursor_row = ?assert_type(Row - 1, non_neg_integer()), cursor_col = length(CurrentLine)});
        _ ->
            State
    end.

-spec handle_arrow_left(state()) -> state().
handle_arrow_left(State) ->
    #state{cursor_col = Col} = State,
    case Col > 0 of
        true -> update_display(State, State#state{cursor_col = Col - 1});
        false -> State
    end.

-spec handle_arrow_right(state()) -> state().
handle_arrow_right(State) ->
    #state{lines = Lines, cursor_row = Row, cursor_col = Col} = State,
    CurrentLine = lists:nth(?assert_type(Row + 1, pos_integer()), Lines), % FIXME TE
    case Col < length(CurrentLine) of
        true -> update_display(State, State#state{cursor_col = Col + 1});
        false -> State
    end.


-spec handle_home(state()) -> state().
handle_home(State) ->
    update_display(State, State#state{cursor_col = 0}).

-spec handle_end(state()) -> state().
handle_end(State) ->
    #state{lines = Lines, cursor_row = Row} = State,
    CurrentLine = lists:nth(?assert_type(Row + 1, pos_integer()), Lines), % FIXME TE
    update_display(State, State#state{cursor_col = length(CurrentLine)}).

-spec handle_arrow_up(state()) -> state().
handle_arrow_up(State) -> % FIXME TE ?
    #state{history = History, history_index = Index} = State,
    case History of
        [] -> State;
        _ ->
            NewIndex = case Index of
                none -> 0;
                I when I + 1 < length(History) -> I + 1;
                _ -> 0
            end,
            CommandLines = lists:nth(?assert_type(NewIndex + 1, pos_integer()), History), % FIXME TE
            NewState = State#state{
                lines = CommandLines,
                cursor_row = length(CommandLines) - 1,
                cursor_col = length(lists:last(CommandLines)),
                history_index = NewIndex
            },
            update_display(State, NewState)
    end.

-spec handle_arrow_down(state()) -> state().
handle_arrow_down(State) ->
    #state{history = History, history_index = Index} = State,
    case History of
      [] -> State;
      _ ->
      case Index of
          none -> 
              NewIndex = length(History) - 1,
              CommandLines = lists:nth(?assert_type(NewIndex + 1, pos_integer()), History), % FIXME TE
              NewState = State#state{
                  lines = CommandLines,
                  cursor_row = length(CommandLines) - 1,
                  cursor_col = length(lists:last(CommandLines)),
                  history_index = NewIndex
              },
              update_display(State, NewState);
          I when I - 1 >= 0 ->
              NewIndex = I - 1,
              CommandLines = lists:nth(?assert_type(NewIndex + 1, pos_integer()), History), % FIXME TE
              NewState = State#state{
                  lines = CommandLines,
                  cursor_row = length(CommandLines) - 1,
                  cursor_col = length(lists:last(CommandLines)),
                  history_index = NewIndex
              },
              update_display(State, NewState);
          _ ->
              NewState = State#state{
                  lines = [""],
                  cursor_row = 0,
                  cursor_col = 0,
                  history_index = none
              },
              update_display(State, NewState)
      end
    end.


-spec nl() -> _.
nl() ->
  io:format("\n\r").


-spec handle_enter(state()) -> state().
handle_enter(State) ->
    #state{lines = Lines, history = History} = State,
    CurrentLine = lists:last(Lines),
    case lists:suffix(";;", CurrentLine) of
        true ->
            % save command to history
            NewHistory = case History of
                [Lines | _] -> History; % don't save duplicates
                _ -> [Lines | History]
            end,
            save_history(NewHistory),
            nl(),
            Str = string:join(Lines, "\n"),
            handle_command(lists:sublist(Str, length(Str) - 2)), % remove ;;
            nl(),
            NewState = State#state{
                lines = [""],
                cursor_row = 0,
                cursor_col = 0,
                history = NewHistory,
                history_index = none
            },
            update_display(NewState, NewState);
        false ->
            % add new line for continuation
            NewState = State#state{
                lines = Lines ++ [""],
                cursor_row = length(Lines),
                cursor_col = 0
            },
            update_display(State, NewState) % FIXME TE ?
    end.

-spec handle_tab(state()) -> state().
handle_tab(State) ->
    #state{lines = Lines, cursor_row = Row} = State,
    Line = string:join(Lines, "\n"),
    case expand_fun(Line) of
        {yes, Completion, []} ->
            CurrentLine = lists:nth(?assert_type(Row + 1, pos_integer()), Lines) ++ Completion, % non_neg_integer + 1
            NewLines = ?assert_type(lists:reverse([CurrentLine | tl(lists:reverse(Lines))]), nonempty_list(string())), % FIXME TE
            NewState = State#state{
                lines = NewLines,
                cursor_col = length(CurrentLine)
            },
            update_display(State, NewState);
        {yes, "", List} ->
            % show multiple matches
            nl(),
            ?assert_type(io:format("~s", [lists:join("   ", [ io_lib:format(color("~s", teal), [C]) || C <- List])]), any()),
            nl(),
            update_display(State, State);
        {no, _, _} ->
            State;
        _ -> error(badarg) % FIXME TE improve spec
    end.

-spec handle_command(string()) -> _.
handle_command("clear") ->
    io:format("\e[2J\e[H"),  % clear screen
    ?PRINT_VERSION;
handle_command("q") ->
    io:format("Exiting...~n\r"),
    % io:put_chars("\e[?1049l"), %% disable alternate screen buffer
    exit(0);
handle_command("help") ->
    io:format(color("Available commands:~n\r", green)),
    lists:foreach(fun(Cmd) -> 
        io:format(color("  ~s~n\r", yellow), [Cmd]) 
    end, ?COMMANDS),
    nl(),
    io:format("Commands terminate with ;;\n\r"),
    io:format("Auto-complete with tab\n\r"),
    ok;
handle_command(Command) ->
    case ast_parser:parse_command(Command) of
        error ->
            io:format(color("Unknown command: ~s~n\r", red), [Command]),
            io:format("Type " ++ color("help;;", yellow) ++ " for available commands~n\r");
        {ok, C = {type_definition, _}} ->
            handle_type_definition(C);
        {ok, C = {subtype, _, _}} ->
            handle_is_subtype(C);
        {ok, C = {equal, _, _}} ->
            handle_is_equal(C);
        {ok, C = {tally_satisfiability, _}} ->
            handle_tally_satisfiability(C);
        {ok, C = {type, _}} ->
            handle_type(C)
    end.

-spec handle_type_definition(ast_parser:command_type_definition()) -> _.
handle_type_definition({type_definition, Definition}) ->
    io:format(color("Type definition:\n\r", yellow)),
    io:format("~p\n\r", [Definition]).

-spec handle_type(ast_parser:command_type()) -> _.
handle_type({type, Type}) ->
    io:format(color("AST representation:\n\r", yellow)),
    io:format("~p\n\r", [Type]),
    Node = ty_parser:parse(Type),
    io:format(color("Internal representation:\n\r", yellow)),
    io:format("~p\n\r", [Node]),
    Unparsed = ty_parser:unparse(Node),
    io:format(color("Unparsed AST representation:\n\r", yellow)),
    io:format("~p\n\r", [Unparsed]),
    Pretty = pretty:render_ty(Unparsed),
    io:format(color("String representation:\n\r", yellow)),
    io:format("~s\n\r", [Pretty]).

-spec handle_is_subtype(ast_parser:command_subtype()) -> _.
handle_is_subtype({subtype, Left, Right}) ->
    LeftTy = ty_parser:parse(Left),
    RightTy = ty_parser:parse(Right),
    Result = ty:is_empty(ty:difference(LeftTy, RightTy)),
    PrettyLeft = pretty:render_ty(ty_parser:unparse(LeftTy)),
    PrettyRight = pretty:render_ty(ty_parser:unparse(RightTy)),
    io:format("~s <= ~s\n\r~p\n\r", [PrettyLeft, PrettyRight, Result]).

-spec handle_is_equal(ast_parser:command_equal()) -> _.
handle_is_equal({equal, Left, Right}) ->
    LeftTy = ty_parser:parse(Left),
    RightTy = ty_parser:parse(Right),
    Result = ty:is_equivalent(LeftTy, RightTy),
    PrettyLeft = pretty:render_ty(ty_parser:unparse(LeftTy)),
    PrettyRight = pretty:render_ty(ty_parser:unparse(RightTy)),
    io:format("~s = ~s\n\r~p\n\r", [PrettyLeft, PrettyRight, Result]).

-spec handle_tally_satisfiability(ast_parser:command_tally_satisfiability()) -> _.
handle_tally_satisfiability({tally_satisfiability, SetOfConstraints}) ->
    Internal = [{ty_parser:parse(T1), ty_parser:parse(T2)} || {T1, T2} <- SetOfConstraints],
    Result = etally:is_tally_satisfiable(Internal, #{}), % TODO parse monomorphic variables
    io:format("~p\n\r", [Result]).

-spec expand_fun(string()) -> {no, nil, nil} | {yes, string(), [string()]}.
expand_fun(Line) ->
    case lists:suffix(";;", Line) of
        true ->
            {no, nil, nil}; 
        false ->
            expand_fun(Line, ?COMMANDS)
    end.

% TODO more precise spec
-spec expand_fun(string(), [string()]) -> {no, nil, nil} | {yes, string(), [string()]}.
expand_fun("", Commands) ->
    {yes, "", Commands};
expand_fun(Line, Commands) ->
    expand_fun(Line, Commands, []).

-spec expand_fun(string(), [string()], [string()]) -> {no, nil, nil} | {yes, string(), [string()]}.
expand_fun(_Line, [], []) ->
    {no, nil, nil};
expand_fun(_Line, [], [Match]) ->
    {yes, Match, []};
expand_fun(_Line, [], Matches) ->
    {yes, "", Matches};
expand_fun(Line, [Cmd | Rest], Matches) ->
    case lists:prefix(Line, Cmd) of
        true ->
            CompletePart = lists:reverse(lists:reverse(Cmd) -- Line),
            expand_fun(Line, Rest, [CompletePart | Matches]);
        false ->
            expand_fun(Line, Rest, Matches)
    end.

-spec clear_line() -> _.
clear_line() ->
    io:format("\e[2K\r").

-spec print_prompt() -> _.
print_prompt() ->
    io:format("> ").

-spec print_prompt(Continuation :: boolean()) -> _.
print_prompt(true) -> io:format("  ");
print_prompt(false) -> io:format("> ").

-spec get_key() -> [char()].
get_key() ->
    case io:get_chars("", 1) of
        {error, _} -> error(badarg);
        'eof' -> error(badarg);
        [27] -> % escape sequence
            More = ?assert_type(io:get_chars("", 3), [char()]),
            [27 | More]; % FIXME TE get_chars can error
        Chars ->
            ?assert_type(Chars, string()) % FIXME TE get_chars can also return unicode binary
    end.

-spec split_at(list(A), non_neg_integer()) -> {list(A), list(A)}.
split_at(List, N) when N =< 0 -> {[], List};
split_at(List, N) when N >= length(List) -> {List, []};
split_at(List, N) -> lists:split(N, List).


-spec save_history([list(string())]) -> _.
save_history(History) ->
    FilePath = history_file_path(),
    case FilePath of 
      no_history -> ok;
      _ ->
        Dir = filename:dirname(FilePath),
        ?assert_pattern(ok, filelib:ensure_dir(?assert_type(Dir, string()) ++ "/")), % FIXME strings
        Formatted = io_lib:format("~p.~n", [History]),
        file:write_file(FilePath, ?assert_type(Formatted, string()))
    end.

-spec load_history() -> history().
load_history() ->
    FilePath = history_file_path(),
    case FilePath of
      no_history -> [];
      _ ->
        case file:consult(FilePath) of 
            {ok, [History]} when is_list(History) -> ?assert_type(History, history()); % this won't hold for history upgrades
            _ -> 
              io:format(color("Bad history file\n\r", red)),
              []
        end
    end.

-spec history_file_path() -> no_history | string().
history_file_path() ->
    case os:getenv("XDG_CACHE_HOME") of
        false ->
            io:format(color("XDG_CACHE_HOME not set, history persistance disabled\n\r", red)),
            no_history;
        XDG_CACHE_HOME -> ?assert_type(filename:join(XDG_CACHE_HOME, ?HISTORY_FILE), string()) % FIXME TE
    end.

-spec replace_at
  (list(T), non_neg_integer(), T) -> list(T);
  (nonempty_list(T), non_neg_integer(), T) -> nonempty_list(T).
replace_at(List, Index, Value) -> 
    % TODO document: what invariant do we need for the REPL that is used here?
    {Before, [_ | After]} = ?assert_pattern({_, [_ | _]}, lists:split(Index, List)), 
    Before ++ [Value] ++ After.


-spec color(string(), atom()) -> string().
color(Str, red) -> "\e[0;31m" ++ Str ++ "\e[0m";
color(Str, green) -> "\e[0;32m" ++ Str ++ "\e[0m";
color(Str, yellow) -> "\e[0;33m" ++ Str ++ "\e[0m";
color(Str, teal) -> "\e[0;36m" ++ Str ++ "\e[0m".

