-module(reduce).

% Skeleton code for reduce algorithm borrowed from UBC's CPSC 521, type information added on

-export([create/2, child_pids/1, parent_pid/1, proc_index/1]).
-export([reduce/3, reduce_test/2, start/0]).

-include_lib("eunit/include/eunit.hrl").

% Type Definitions ------------------------------------------------------------------

-type procInfo() :: {
    PPid :: pid() | {pid()},
    CPids :: [pid()],
    I :: non_neg_integer()
}.

-type task() :: fun((procInfo()) -> atom()).
-type combine(DataT) :: fun((DataT, DataT) -> DataT).

% Accessors -------------------------------------------------------------------------

-spec child_pids(procInfo()) -> [] | [pid()].
child_pids({_, CPids, _}) -> CPids.

-spec parent_pid(procInfo()) -> pid() | {pid()}.
parent_pid({PPid, _, _}) -> PPid.

-spec proc_index(procInfo()) -> non_neg_integer().
proc_index({_, _, I}) -> I.

% Node Creation ---------------------------------------------------------------------

-spec create(pos_integer(), task()) -> pid().
create(NProcs, Task) when
    is_integer(NProcs), 0 < NProcs, is_function(Task, 1)
->
    MyPid = self(),
    spawn(fun() -> create(NProcs, {MyPid}, 1, [], Task) end).

-spec create(pos_integer(), pid() | {pid()}, non_neg_integer(), [pid()], task()) -> pid().
create(1, Parent, MyIndex, ChildPids, Task) ->
    Task({Parent, ChildPids, MyIndex});
create(N, Parent, MyIndex, ChildPids, Task) when is_integer(N), 1 < N ->
    NLeft = N div 2,
    NRight = N - NLeft,
    MyPid = self(),
    RightPid = spawn(fun() ->
        create(NRight, MyPid, MyIndex + NLeft, [], Task)
    end),
    create(NLeft, Parent, MyIndex, [RightPid | ChildPids], Task).

% Reduce ----------------------------------------------------------------------------

-spec reduce(procInfo(), combine(DT), DT) -> DT.
reduce(ProcInfo, CombineFun, Value) ->
    reduce(parent_pid(ProcInfo), child_pids(ProcInfo), CombineFun, Value).

-spec reduce(pid() | {pid()}, [pid()], combine(DT), DT) -> DT.
reduce({_}, [], _, GrandTotal) ->
    GrandTotal;
reduce(ParentPid, [], _, MyTotal) ->
    ParentPid ! {self(), reduce_up, MyTotal},
    receive
        {ParentPid, reduce_down, GrandTotal} -> GrandTotal
    end;
reduce(Parent, [ChildHd | ChildTl], CombineFun, LeftTotal) ->
    receive
        {ChildHd, reduce_up, RightTotal} ->
            GrandTotal =
                reduce(Parent, ChildTl, CombineFun, CombineFun(LeftTotal, RightTotal)),
            ChildHd ! {self(), reduce_down, GrandTotal},
            GrandTotal
    end.

% Test ------------------------------------------------------------------------------

red_fun() -> fun(X, Y) -> X + Y end.
red_fun_buggy() -> fun(X, Y) -> X + Y / 2 end.

reduce_test(NProcs, Fun) when is_integer(NProcs), 0 < NProcs ->
    MasterPid = self(),
    create(
        NProcs,
        fun(ProcInfo) ->
            I = proc_index(ProcInfo),
            Total = reduce(ProcInfo, Fun, I),
            case I of
                1 -> MasterPid ! {self(), reduce_test, Total};
                _ -> ok
            end
        end
    ),
    V =
        receive
            {Pid, reduce_test, Total} when is_pid(Pid) -> Total
        after 1000 -> time_out
        end,
    [H | T] = lists:reverse(lists:seq(1, NProcs)),
    ?assertEqual(lists:foldl(Fun, H, T), V).

start() -> reduce_test(100, red_fun()), reduce_test(100, red_fun_buggy()).