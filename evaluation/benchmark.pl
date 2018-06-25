:-use_module(library(clpfd)).
:-ensure_loaded('../ite.pl').

pre(Time, Space) :-
  statistics(walltime, [Time|_]),
  statistics(heap, [Space|_]).

post(Vars, Time0, Space0) :-
  statistics(walltime, [T1|_]),
  statistics(heap, [S1|_]),
  Time is T1 - Time0,
  Space is S1 - Space0,
  
  format("time:~d~n", [Time]),
  format("space:~d~n", [Space]),
  
  ( foreach(V, Vars)
  do
    fd_size(V, VSize),
    format("domain:~p~n", [VSize])
  ),
  fd_statistics(resumptions, Resumptions),
  format("resumptions:~d~n", [Resumptions]),
  fd_statistics(entailments, Entailments),
  format("entailments:~d~n", [Entailments]),
  fd_statistics(prunings, Prunings),
  format("prunings:~d~n", [Prunings]),
  fd_statistics(backtracks, Backtracks),
  format("backtracks:~d~n", [Backtracks]),
  fd_statistics(constraints, Constraints),
  format("constraints:~d~n", [Constraints]).
