%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% constraints.pl - Author: Arnaud Gotlieb, Helge Spieker (2019/04/22)  - SIMULA RESEARCH LABORATORY
% Benchmarking of ITE with global constraints implementations
%
% Ultrametric constraint with ITE   [Moore Prosser, The Ultrametric Constraint and its Application to Phylogenetics, JAIR 32 2008 901-938]
% Domain constraint with ITE  [Refalo, CP'2000]
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- ensure_loaded(['../ite.pl']).
:- use_module(library(timeout)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ULTRAMETRIC Constraint
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
um3(cd, X, Y, Z, ENV) :-
        (X #> Y, Y = Z) cd (Y #> Z, X = Z) cd (Z #> X, X =Y) cd (X = Y, Y = Z).

um3(cd(K), X, Y, Z, ENV):-
        cd(cd((X #> Y, Y = Z), (Y #> Z, X = Z), ENV), cd((Z #> X, X =Y), (X = Y, Y = Z), ENV), ENV).

um3(reg, X, Y, Z, ENV) :-
        (X #> Y #/\ Y #= Z)   #\/  (Y #> Z #/\ X #= Z)  #\/  (Z #> X  #/\  X #=Y) #\/  (X #= Y #/\ Y #= Z).

um3(smt, X, Y, Z, ENV) :-
         smt((X #> Y #/\ Y #= Z)   #\/  (Y #> Z #/\ X #= Z)  #\/  (Z #> X  #/\  X #=Y) #\/  (X #= Y #/\ Y #= Z)).

% Ultrametric Matrix
mum(OP, M, L, ENV) :-
        X2 in -1000000..7, X3 in 7..1000000, X4 in 1..1000000, Y3 in 0..1000000, Y4 in 0..1000000, Z4 in 0..1000000,
        L = [X2, X3, X4, Y3, Y4, Z4],
%        domain(L,  MIN, MAX),
        M = [[0, X2, X3, X4], [X2, 0, Y3, Y4], [X3, Y3, 0, Z4], [X4, Y4, Z4, 0]],
        um3(OP, X2, X3, X4, ENV),
        um3(OP, X2, X3, Y3, ENV),
        um3(OP, X2, X3, Y4, ENV),
        um3(OP, X2, X3, Z4, ENV),
        um3(OP, X2, X4, Y3, ENV),
        um3(OP, X2, X4, Z4, ENV),
        um3(OP, X2, Y3, Y4, ENV),
        um3(OP, X2, Y3, Z4, ENV),
        um3(OP, X2, Y4, Z4, ENV).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DOMAIN(X,[X1, .., Xn]) is true   iff   (X = i iff   Xi = 1)    % equivalent to bool_channel(L, X, #=, 0)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 % OP must be either   cd, reg, smt, cd(K)
domctr(OP, X, L, ENV) :-
        length(L, N),
        X in 1..N,
        domain(L, 0,1),
        domctr(OP, N, X, L, ENV).

domctr(_OP, 1, X, [X1], _ENV) :- !, X=1, X1=1.

%%%%%
% cd
domctr(cd, 2, X, [X1,X2], _ENV) :- !,  cd((X=1,X1=1, X2=0), (X=2, X1=0, X2=1)).
domctr(cd(_K), 2, X, [X1,X2], ENV) :- !, cd((X=1,X1=1, X2=0), (X=2, X1=0, X2=1), ENV).
domctr(cd, N, X, [X1|L], ENV) :- N > 2, !,
        N1 is N-1,
        cd((X=1, X1=1, domain(L,0,0)), (X#>1, X1=0, Y in 1..N1, incr(X,Y), domctr(cd, N1, Y, L, ENV))). 
domctr(cd(K), N, X, [X1|L], ENV) :- N > 2, !,
        N1 is N-1,
        cd((X=1, X1=1, domain(L,0,0)), (X#>1, X1=0, Y in 1..N1, incr(X,Y), domctr(cd(K), N1, Y, L, ENV)), ENV).

%%%%%
% reg: #\/
domctr(reg, N, X, L, _ENV) :- !, lists:reverse(L, L1),
        domctr1(N, X, L1, T),
        call(T).
%%%%%
% reg: smt
domctr(smt, N, X, L, _ENV) :- !, lists:reverse(L, L1),
        domctr1(N, X, L1, T),
        call(smt(T)).

%%%%%%%
% global
domctr(global, N, X, L, _ENV):-
        bool_channel(L, X, #=, 0).

domctr1(2, X, [X1,X2], T) :- !,  T = #\/(  (X#=1 #/\ X1#=1 #/\ X2#=0),  (X#=2 #/\ X1#=0 #/\ X2#=1) ).
%domctr1(3, X, [X1,X2,X3], T) :- !,  T = ((X#=1 #/\ X1#=1 #/\ X2#=0 #/\ X3#=0) #\/ (X#=2 #/\ X1#=0 #/\ X2#=1 #/\ X3#=0) #\/ (X#=3 #/\ X1#=0 #/\ X2#=0 #/\ X3#=1)).
domctr1(N, X, L, T) :-   N>2,  !,
        domctr2(1, N, X, L, T).

domctr2(N, N, X, L, T1):-  !,
        domctr3(N, N, X, L, T1).
domctr2(M, N, X, L,   (T1) #\/ Ts) :-  M < N,  !,
        M1 is M+1,
        domctr3(M, N, X, L, T1),
        domctr2(M1,N, X, L, Ts).

domctr3(M, 0, X, [], X#=M) :- !.
domctr3(M, K, X, [X1|L],  X1#=B #/\ T ) :-  K>=1,  !,
        (K == M -> B=1 ; B=0),
        K1 is K-1,
        domctr3(M, K1, X, L, T).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% The pitfall of bound-consistency
% | ?- Y in {1}\/{9999}, X #= Y+1.
%   Y in{1}\/{9999},
%   X in 2..10000 ? 

% | ?- Y in {1}\/{9999}, incr(X,Y).
% Y in{1}\/{9999},
% X in{2}\/{10000}

incr(X, Y) +:
        X in dom(Y) + 1,
        Y in dom(X) -1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%    ELEMENT(I, [X1,..,Xn], J) is true iff   or(and(I=1,J=X1),..,and(I=n, J=Xn))
%
% | ?- X3 in 4..6, X1 in 1..2, X2 in 56..78, J in 5..63, elemctr(cd, I, [X1, X2, X3], J).
%   X3 in 4..6,
%   X1 in 1..2,
%   X2 in 56..78,
%     J in(5..6)\/(56..63),
%     I in 2..3 ? 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 % OP must be either   cd, reg, smt, cd(K), global
elemctr(OP, I, L, J, ENV):-
        length(L, N),
         I in 1..N,
        elemctr(OP, N, I, L, J, ENV).

elemctr(_OP, 1, I, [X1], J, _ENV) :- !, I=1, J #= X1.
elemctr(global, _N, I, L, J, _ENV) :- !, element(I, L, J).   % maintain only bound-consistency in L and J

% cd
elemctr(cd, 2, I, [X1, X2], J, _ENV) :- !, cd( (I=1, J #= X1), (I=2, J #= X2) ).
elemctr(cd, N, I, [X1|L], J, ENV) :- N > 2, !,
        N1 is N-1,
        cd((I=1, X1#=J), (I #> 1, I1 in 1..N1, incr(I, I1), elemctr(cd, N1, I1, L, J, ENV))). 

% cd(K)
elemctr(cd(_K), 2, I, [X1, X2], J, ENV) :- !, cd( (I=1, J #= X1), (I=2, J #= X2), ENV).
elemctr(cd(K), N, I, [X1|L], J, ENV) :- N > 2, !,
        N1 is N-1,
        cd((I=1, X1#=J), (I #> 1, I1 in 1..N1, incr(I, I1), elemctr(cd(K), N1, I1, L, J, ENV)), ENV). 

% reg
elemctr(reg, N, I, L, J, _ENV):-
        elemctr2(1, N, I, L, J, T),
        call(T).
elemctr2(N, N, I, [XN], J, (I #= N #/\ J#=XN)) :-!.
elemctr2(M, N, I, [X|Xs], J, (I #= M #/\ X  #= J) #\/ T) :-  M < N, !,
        M1 is M+1,
        elemctr2(M1, N, I, Xs, J, T).

% smt
elemctr(smt, N, I, L, J, _ENV):-
        elemctr2(1, N, I, L, J, T),
        call(smt(T)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%    LEX([X1,..,Xn], [Y1, .., Yn]) is true iff   X1 < Y1 or (X1=Y1 and X2 < Y2) or (X1=Y1 and X2=Y2 and X3 < Y3) ... 
                                %
% | ?- X1 in 2..3, Y1 in 0..2, X2 in 3..4, Y2 in 0..5, lexctr(cd, [X1,X2], [Y1, Y2]).
% X1 = 2, Y1 = 2, X2 in 3..4, Y2 in 4..5 ? 
% 
% | ?- X1 in 1..2, X2 in 6..7, X3 in 5..6, Y1 in 0..1, Y2 in 2..9, Y3 in 0..1, lexctr(cd, [X1, X2, X3], [Y1,Y2,Y3]).
% X1 = 1, Y1 = 1, X2 in 6..7, X3 in 5..6, Y2 in 7..9, Y3 in 0..1 ? 

% OP must be either   cd, reg, smt, cd(K), global

% cd
lexctr(cd, X, Y, ENV):-
        X = [X1|Xs], Y = [Y1|Ys],
        lexctr(cd, Xs, Ys, [X1], [Y1], fail, T, ENV),
        call(cd(X1 #<Y1, T)).

% cd(K)
lexctr(cd(K), X, Y, ENV):-
        X = [X1|Xs], Y = [Y1|Ys],
        lexctr(cd(K), Xs, Ys, [X1], [Y1], fail, T, ENV),
        call(cd(X1 #< Y1, T, ENV)).


lexctr(_OP, [], [], _LX, _LY, TIN, TIN, _ENV) :- !.
lexctr(cd, [X|Xs], [Y|Ys], LX, LY, TIN, cd(T, TOUT), ENV) :-
        gen_eq(cd, LX, LY, T1) ,
        T = (X #< Y, T1),
        lexctr(cd, Xs, Ys, [X|LX], [Y|LY], TIN, TOUT, ENV).

lexctr(cd(K), [X|Xs], [Y|Ys], LX, LY, TIN, TOUT, ENV) :-
        gen_eq(cd, LX, LY, T1),
        T = cd(TIN, (X #< Y, T1), ENV),
        lexctr(cd(K), Xs, Ys, [X|LX], [Y|LY], T, TOUT, ENV).

gen_eq(cd, [X], [Y], (X #= Y)) :- !.
gen_eq(cd, [X|Xs], [Y|Ys], (X #= Y, T)) :-
        gen_eq(cd, Xs, Ys, T).

 % reg
lexctr(reg, X, Y, ENV):-
        X = [X1|Xs], Y = [Y1|Ys],
        lexctr(reg, Xs, Ys, [X1], [Y1], (X1 #< Y1), T, ENV),
        call(T).

lexctr(reg, [X|Xs], [Y|Ys], LX, LY, TIN, TOUT, ENV) :-
        gen_eq(reg, LX, LY, T1),
        T = (TIN #\/  (X #< Y #/\ T1)),
        lexctr(reg, Xs, Ys, [X|LX], [Y|LY], T, TOUT, ENV).

gen_eq(reg, [X], [Y], (X #= Y)) :- !.
gen_eq(reg, [X|Xs], [Y|Ys], (X #= Y #/\ T)) :-
        gen_eq(reg, Xs, Ys, T).

% smt
lexctr(smt, X, Y, ENV):-
        X = [X1|Xs], Y = [Y1|Ys],
        lexctr(reg, Xs, Ys, [X1], [Y1], (X1 #< Y1), T, ENV),
        call(smt(T)).

%global
lexctr(global, X, Y, _ENV):-
        lex_chain([X, Y], [global(true)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
%    MUL(N, X, Min, Max) is true iff   X #>= Min and (X #= N*1 or X #= N*2 or ... or X #= N*M) and X #=< Max  
%
% | ?- X in 0..100000, N = 47, mulctr(N, X, 178, 5689, E).
%

mulctr(OP, N, X, Min, Max, ENV) :-
        X #>= Min, X #=< Max,
        fd_max(X, Xmax), fd_max(N, Nmax),
        Mmax is Xmax div Nmax,
        gen_mulctr(1, Mmax, N, X, [], L),
        mulctr1(OP, L, T, ENV),
        (OP = smt -> call(smt(T)) ; call(T)).

gen_mulctr(M, M, _N, _X, L, L):-!.
gen_mulctr(M, Mmax, N, X, T, [X #= M*N|Xs]) :-
        M1 is M+1,
       gen_mulctr(M1, Mmax, N, X, T, Xs).

mulctr1(_OP, [CTR], CTR, _ENV) :-!.
mulctr1(cd, [CTR|S], cd(CTR, CS), ENV):-!,
        mulctr1(cd, S, CS, ENV).
mulctr1(cd(K), [CTR|S], cd(CTR, CS, ENV),  ENV):-!,
        mulctr1(cd(K), S, CS,  ENV).
mulctr1(reg, [CTR|S], CTR #\/ CS, ENV):-!,
        mulctr1(reg, S, CS, ENV).
mulctr1(smt, [CTR|S], CTR #\/ CS, ENV):-!,
        mulctr1(smt, S, CS, ENV).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DISTANCE([X1, .., Xn], K) iff abs(X1, X2) >= K and abs(X1, X3) >= K, ..., abs(Xn-1, Xn) >= K
%                                                 not( not(X1-X2>=K and X2-X1>=K) or ... or  not(Xn-1 - Xn>=K and Xn - Xn-1>=K)) 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
distctr(OP, L, K, ENV) :-
        gen_dist(OP, L, K, G, ENV),
        call(G).

gen_dist(OP, [_], K, true, _ENV):- !.
gen_dist(OP, [X|XL], K, (G1, G), ENV) :-
        gen_dist1(OP, X, XL, K, G1, ENV),
        gen_dist(OP, XL, K, G, ENV).
        
gen_dist1(cd, X, [Y], K,   cd(X-Y #>= K, Y-X #>= K), _ENV ) :-!.
gen_dist1(cd, X, [Y|YL], K,   (cd(X-Y #>= K, Y-X #>= K), G), ENV):-
        gen_dist1(cd, X, YL, K, G, ENV).

gen_dist1(cd(K), X, [Y], K1,  cd(X-Y #>= K1,  Y-X #>= K1, ENV), ENV ) :-!.
gen_dist1(cd(K), X, [Y|YL], K1, (cd(X-Y #>= K1, Y-X #>= K1, ENV), G), ENV):-
        gen_dist1(cd(K), X, YL, K1, G, ENV).

gen_dist1(reg, X, [Y], K, (X-Y #>= K #\/ Y-X #>= K), _ENV ) :-!.
gen_dist1(reg, X, [Y|YL], K, ((X-Y #>= K #\/ Y-X #>= K), G), ENV):-
        gen_dist1(reg, X, YL, K, G, ENV).

gen_dist1(smt, X, [Y], K, smt(X-Y #>= K #\/ Y-X #>= K), _ENV ) :-!.
gen_dist1(smt, X, [Y|YL], K, (smt(X-Y #>= K #\/ Y-X #>= K), G), ENV):-
        gen_dist1(smt, X, YL, K, G, ENV).

gen_dist1(global, X, [Y], K, abs(X-Y) #>= K, _ENV ) :-!.
gen_dist1(global, X, [Y|YL], K, (abs(X-Y) #>= K, G), ENV):-
        gen_dist1(global, X, YL, K, G, ENV).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% The constraint DISJUNCTIVE([S1,..,Sn]) is true iff   Si + pi =< Sj   OR   Sj + pj  =< Si    for all pairs of tasks i <> j.
% OP=cd, cd(K), cxd, reg
%  H: Horizon = sum(Si+Pi) for all i
%  S: List of start time (Variables)
% P: List of durations   - S and P must have the same length 
%
%  ?- OP = cxd, S1 in 1..3, P1=2, S2 in 2..5, P2=3,  disjctr(OP, [S1,S2], [P1,P2], H), labeling([minimize(H)], [S1,S2]).
%    S1=1,   S2=3,  H=9
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
disjctr(OP, S, P, H, ENV) :-
        joinsp(S, P, SP),
        gen_disj(OP, SP, G, ENV),
        append(S, P, VSP),
        sum(VSP, #=, H),
        call(G).

joinsp([], [], []).
joinsp([X|Xs], [Y|Ys], [(X,Y)|S]) :-
        joinsp(Xs, Ys, S).

gen_disj(_OP, [_], true, _ENV):- !.
gen_disj(OP, [X|XL], (G1, G), ENV) :-
        gen_disj1(OP, X, XL, G1, ENV),
        gen_disj(OP, XL, G, ENV).
        
gen_disj1(cd, (Si,Pi), [(Sj,Pj)], (Si+Pi #=< Sj   cd  Sj+Pj #=< Si), _ENV ) :-!.
gen_disj1(cd, (Si,Pi), [(Sj,Pj)|YL], ((Si+Pi #=< Sj cd Sj+Pj #=< Si), G), ENV):-
        gen_disj1(cd, (Si,Pi), YL, G, ENV).

gen_disj1(cxd, (Si,Pi), [(Sj,Pj)], (Si+Pi #=< Sj   cxd  Sj+Pj #=< Si), _ENV ) :-!.
gen_disj1(cxd, (Si,Pi), [(Sj,Pj)|YL], ((Si+Pi #=< Sj  cxd  Sj+Pj #=< Si), G), ENV):-
        gen_disj1(cxd, (Si,Pi), YL, G, ENV).

gen_disj1(cd(K), (Si,Pi), [(Sj,Pj)], cd(Si+Pi #=< Sj, Sj+Pj #=< Si, ENV),  ENV ) :-!.
gen_disj1(cd(K), (Si,Pi), [(Sj,Pj)|YL], (cd(Si+Pi #=< Sj, Sj+Pj #=< Si, ENV), G),  ENV):-
        gen_disj1(cd(K), (Si,Pi), YL, G,  ENV).

gen_disj1(reg, (Si,Pi), [(Sj,Pj)], (Si+Pi #=< Sj   #\/  Sj+Pj #=< Si), _ENV ) :-!.
gen_disj1(reg, (Si,Pi), [(Sj,Pj)|YL], ((Si+Pi #=< Sj  #\/  Sj+Pj #=< Si), G), ENV):-
        gen_disj1(reg, (Si,Pi), YL, G, ENV).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%% UTILS  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
random_list(Size, _M, []):-  Size =< 0, !.
random_list(Size, M, [X|Xs]) :-
        random(1, M, X),
        Size1 is Size - 1,
        random_list(Size1, M, Xs).

%%%%%%%%%%%%%%%%%%  IN/OUT  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
print_results(success, Benchmark, OP, M, N, T, Mem) :-
  !,
  write(Benchmark), write(';'), write(N), write(';'), write(OP), write(';'), write(M), write(';'), write(T), write(';'), write(Mem),
  print_statistics.
print_results(time_out, Benchmark, OP, _M, N, T, Mem) :-
  !,
  write(Benchmark), write(';'), write(N), write(';'), write(OP), write(';timeout;'), write(T), write(';'), write(Mem),
  print_statistics.
print_results(fail, Benchmark, OP, _M, N, T, Mem) :-
  !,
  write(Benchmark), write(';'), write(N), write(';'), write(OP), write(';fail;'), write(T), write(';'), write(Mem),
  print_statistics.
print_statistics :-
  fd_statistics(resumptions, Resumptions),
  fd_statistics(entailments, Entailments),
  fd_statistics(prunings, Prunings),
  fd_statistics(backtracks, Backtracks),
  fd_statistics(constraints, Constraints),
  format(';~d;~d;~d;~d;~d~n', [Resumptions, Entailments, Prunings, Backtracks, Constraints]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Benchs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
benchs(domctr2):-    % DOMAIN constraint
        ( N = 100 ; N = 200 ; N = 300 ; N = 400 ; N = 500 ; N = 600 ; N = 700 ; N = 800 ; N = 900 ; N = 1000),
         ( (K=2, OP = cd(K)) ; (K=3, OP = cd(K)) ; OP = cd ; OP = reg ; OP = smt ; OP = global),
        statistics(memory_used, Mem0),
        statistics(runtime, [T0|_]),
        G = (init_env(ENV, [kflag(K), susp(val)]), length(L, N), domctr(OP, X, L, ENV), X*X #< N, labeling([maximize(X)], L), end_env(ENV)),
        (time_out(G, 300000, Result) -> true ; Result =fail),
        statistics(runtime, [T1|_]),
        statistics(memory_used, Mem1),
        T is T1-T0,
        Mem is Mem1-Mem0,
        print_results(Result, domctr2, OP, X, N, T, Mem),
        fail.

benchs(mum) :-    % ULTRAMETRIC Constraint
        ( Options = [leftmost, up, step] ; Options = [max, up, step] ; Options = [leftmost, down, step] ; Options = [max, down, step] ),
        ( (K=2, OP = cd(K)) ; (K=3, OP = cd(K)) ; OP = cd ; OP = reg ; OP = smt),
        nl,
        statistics(runtime, [T0|_]),
        G = (init_env(ENV, [kflag(K), susp(val)]), X in 0..1,   mum(OP, M, L, ENV),  labeling([minimize(X)|Options], [X|L]), end_env(ENV)),
        (time_out(G, 300000, Result) -> true ; Result = fail),
        statistics(runtime, [T1|_]),
        T is T1-T0,
        print_results(Result, OP, M, Options, T),
        fail.

benchs(elemctr1):-    % ELEMENT constraint
         ( (K=1,OP = cd(K)) ; (K=2, OP = cd(K)) ; (K=3, OP = cd(K)) ; (K=4, OP = cd(K)) ; OP = reg ; OP = smt ; OP = global ),
        statistics(runtime, [T0|_]),
                                %        G = (length(L, N), domain([I|L], 0, N), elemctr(OP, I, L, J), elemctr(OP, J, L, K), I #= J, cn(J  #= K), labeling([maximize(J)], [I|L])),
        G = (init_env(ENV, [kflag(K)]), L = [_X1, _X2, _X3, _X4, _X5, _X6, _X7, _X8, _X9, _X10, _X11, _X12, _X13, _X14, _X15, _X16, _X17, _X18, _X20, _X21, _X22, _X23, _X24], elemctr(OP, I, L, J, ENV), _X1 in 402..11349, _X2 in 1374..41391, _X3 in 2379..7299, _X4 in 23423..91368, _X5 in 445..67689, _X6 in 1123..86356, _X7 in 7676..98876, _X8 in 445..18789, _X9 in 565..18796, _X10 in 654..35655, _X11 in 523..91378, _X12 in 4625..88765, _X13 #= _X2*I, _X14 #= _X1*I, _X15 in 1467..67789, _X16 in 43..342,  _X17 in 1257..37810, _X18 in 789..6543, _X19 in 500..34567, _X20 in 1342..65421, _X21 in 4563..7689453, _X22 in 6574..8675433, _X23 in 987..1387654, _X24 in 786..76543, J in 288..495, M #= J*J - I*J - I*I, labeling([maximize(M)], L), end_env(ENV)),
        (time_out(G, 60000, Result) -> true ; Result = fail),
        statistics(runtime, [T1|_]),
        T is T1-T0,
        print_results(Result, OP, M, L, T),
        fail.

benchs(elemctr2):-    % ELEMENT constraint
        ( N = 100 ; N = 140 ; N = 180 ; N = 220 ; N = 260 ; N = 300 ; N = 340 ; N = 380 ; N = 420 ; N = 460),
         ( (K=2, OP = cd(K)) ; (K=3, OP = cd(K)) ; OP = cd ; OP = reg ; OP = smt ; OP = global ),
        statistics(memory_used, Mem0),
        statistics(runtime, [T0|_]),
                                %        G = (length(L, N), domain([I|L], 0, N), elemctr(OP, I, L, J), elemctr(OP, J, L, K), I #= J, cn(J  #= K), labeling([maximize(J)], [I|L])),
        G = (init_env(ENV, [kflag(K)]), length(L, N), domain(L, 2, N), K1 is N*N, J in N..K1, I in 10..N, M #= J*J - I*J - I*I, elemctr(OP, I, L, J, ENV), lists:append(L, [J, I], L1), labeling([maximize(M)], L1), end_env(ENV)),
        (time_out(G, 60000, Result) -> true ; Result = fail),
        statistics(runtime, [T1|_]),
        statistics(memory_used, Mem1),
        T is T1-T0,
        Mem is Mem1-Mem0,
        print_results(Result, elemctr2, OP, (M, [J,I]),N, T, Mem),
        fail.

benchs(lexctr2):-    % LEX constraint - Very unstable results for reg and smt - Don't have any explanation yet.
        ( N = 10 ; N = 20 ; N = 30 ; N = 40 ; N = 50 ; N = 60 ; N = 70 ; N = 80 ; N = 90 ; N = 100),
         ( (K=2,OP = cd(K)) ; (K=3,OP =cd(K)) ; OP = reg ; OP = smt ; OP = global ),
        statistics(memory_used, Mem0),
        statistics(runtime, [T0|_]),
                                %        G = (length(L, N), domain([I|L], 0, N), elemctr(OP, I, L, J), elemctr(OP, J, L, K), I #= J, cn(J  #= K), labeling([maximize(J)], [I|L])),
        G = (init_env(ENV, [kflag(K)]), length(X,N),  length(Y, N), domain(X, 100, 200), domain(Y, 0, 101), lexctr(OP, X, Y, ENV), S1 in 1000..4000, S2 in 1000..4000, sum(X, #>=, S1), sum(Y, #=<, S2), S #= S1*S1-S1*S2-S2*S2, solve([maximize(S)],[labeling([leftmost], [S2|Y]), labeling([leftmost],[S1|X])]), end_env(ENV) ),
        (time_out(G, 60000, Result) -> true ; Result = fail),
        statistics(runtime, [T1|_]),
        statistics(memory_used, Mem1),
        T is T1-T0,
        Mem is Mem1-Mem0,
        print_results(Result, lexctr2, OP, S, N, T, Mem),
        fail.


benchs(mulctr1):-    % MUL constraint benchmarking
        ( (Max = 1000, N=11, M=13, K = 7)  ; (Max = 100000, N=283, M=143, K = 7)),
        (OP = cd(K) ; OP = reg ; OP = smt),
        statistics(runtime, [T0|_]),
        G = (init_env(ENV, [kflag(K)]), mulctr(OP, N, X, 2, Max, ENV), mulctr(OP, M, X, 2, Max, ENV), mulctr(OP, N, Y, 2, Max, ENV), mulctr(OP, M, Y, 2, Max, ENV), S + N*X*Y #= Max, labeling([maximize(S)],[X,Y]), end_env(ENV)),
        (time_out(G, 60000, Result) -> true ; Result = fail),
        statistics(runtime, [T1|_]),
        T is T1-T0,
        print_results(Result, OP, X, Max, T),
        fail.

benchs(mulctr2):-               % MUL constraint benchmarking
        N in 61..62, M in 57..58,
        ( Max = 2000 ; Max = 2200 ; Max = 2400 ; Max = 2600 ; Max = 2800 ; Max = 3000 ; Max = 3200 ; Max = 3400 ; Max = 3600 ; Max = 3800),
        ((K=2,OP = cd(K)) ; (K=3,OP = cd(K)) ; (K=4,OP = cd(K)) ; (K=5,OP = cd(K)) ; (K=6, OP = cd(K)) ; (K=7,OP = cd(K)) ; OP= cd ; OP = reg ; OP = smt),
        statistics(memory_used, Mem0),
        statistics(runtime, [T0|_]),
        G = (init_env(ENV, [kflag(K)]), mulctr(OP, N, X, 2, Max, ENV), mulctr(OP, M, X, 2, Max, ENV), mulctr(OP, N, Y, 2, Max, ENV), mulctr(OP, M, Y, 2, Max, ENV), mulctr(OP, N, Z, 2, Max, ENV), mulctr(OP, M, Z, 2, Max, ENV), mulctr(OP, N, XX, 2, Max, ENV), mulctr(OP, M, XX, 2, Max, ENV), N*X*Y - M*Z*XX #= S, labeling([maximize(S)],[N, M, X,Y,Z,XX]), end_env(ENV)),
        (time_out(G, 60000, Result) -> true ; Result = fail),
        statistics(runtime, [T1|_]),
        statistics(memory_used, Mem1),
        T is T1-T0,
        Mem is Mem1-Mem0,
        print_results(Result, mulctr2, OP, S, Max, T, Mem),
        fail.

benchs(distctr1):-    % DISTANCE constraint benchmarking  % Expected result is FAIL
        (Min = 1, Max = 1000),
        (OP = cd ; (K=2,OP = cd(K)) ; (K=7,OP = cd(K)) ; OP = reg ; OP = smt ; OP = global),
        statistics(runtime, [T0|_]),
        G = (init_env(ENV, [kflag(K), susp(val)]), length(L, 12), domain(L, Min, Max),  C in 110..170, distctr(OP, L, C, ENV), labeling([], L), end_env(ENV)),
        (time_out(G, 360000, Result) -> true ; Result = fail),
        statistics(runtime, [T1|_]),
        T is T1-T0,
        print_results(Result, OP, L, Max, T),
        fail.

benchs(distctr):-    % DISTANCE constraint benchmarking  %
        (M=1 ; M=2 ; M=3; M=4 ; M=5 ; M=6 ; M= 7 ; M=8 ; M=9 ; M=10),
         ((K=1, OP = cd(K)) ;  (K=2, OP = cd(K)) ; (K=3, OP = cd(K)) ; (K=4,OP = cd(K)) ; OP = cd ; OP = reg ; OP = smt ; OP = global),
        statistics(runtime, [T0|_]),
        G = (init_env(ENV, [kflag(K),susp(val)]), length(L, M), M1 is M-1, M2 is M+10, M3 is M*(M-1), domain(L, 1, M3),  C in M1..M2, distctr(OP, L, C, ENV), labeling([maximize(C), down], [C|L]), end_env(ENV)),
        (time_out(G, 60000, Result) -> true ; Result = fail),
        statistics(runtime, [T1|_]),
        T is T1-T0,
        print_results(Result, OP, (C, L), M, T),
        fail.

benchs(disjctr):-    % DISTANCE constraint benchmarking  % Expected result is "Fail"
        Max = 1000,
        (N=1; N=2 ; N=3 ; N=4 ; N=5 ; N=6 ; N=7 ; N=8 ; N=9 ; N=10),   % Number of Tasks
        ((K=1, OP = cd(K)) ; (K=2, OP = cd(K)) ; (K=3, OP = cd(K)) ; OP = cd ; OP = cxd ; OP = reg),
        statistics(runtime, [T0|_]),
        G = (init_env(ENV, [kflag(K)]), length(S, N),  domain(S, 1, Max),  random_list(N, 100, P), disjctr(OP, S, P, H, ENV), labeling([minimize(H), all], S), end_env(ENV)),
        (time_out(G, 60000, Result) -> true ; Result = fail),
        statistics(runtime, [T1|_]),
        T is T1-T0,
        print_results(Result, OP, (S,P,H), N, T),
        fail.


user:runtime_entry(start) :-
  prolog_flag(argv, []),
  write('benchmark;n;op;result;time;resumptions;entailments;prunings;backtracks;constraints;memory'),nl,
  ( benchs(domctr2) -> true ; true ), !,
  ( benchs(elemctr2) -> true ; true ), !,
  ( benchs(lexctr2) -> true ; true ), !,
  ( benchs(mulctr2) -> true ; true ), !.  
  %( benchs(mum) -> true ; true ), !,  % use best labeling option
  %( benchs(disjctr) -> true ; true ), !, % can be discarded
  %( benchs(distctr1) -> true ; true ), !,  % can be discarded
  %( benchs(distctr2) -> true ; true ).
user:runtime_entry(start) :-
  prolog_flag(argv, [Constraint]),
  benchs(Constraint).
