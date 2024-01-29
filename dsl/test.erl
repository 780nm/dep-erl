-module(test).
-export([start/0]).

start() -> reduce:reduce_test(100, fun (A, B) -> apply(apply(fun (X) -> fun (Y) -> X + Y * 0 end end, [A]), [B]) end).