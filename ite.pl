%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ite.pl - Author: Arnaud Gotlieb   (2012/07/01)  - SIMULA RESEARCH LABORATORY
% Vers. 1:    Stratified reasoning - No memoization
% Vers. 1.1:  Adding cxd/2 constructive exclusive disjunction 
%
% An implementation of constructive disjunction (and stratified CD), constructive negation,
% constructive conditional, constructive implication  for clpfd programs. 
% NOTE : - 2012/07/01 - Tested only with SICStus Prolog 4.2.0 on a Windows machine
%        - 2015/09/23 - Tested with SICStus Prolog 4.3.1 on x86_64-win32-nt-4
%
% Syntax on which cd/2, cd/3, cxd/2, cn/1, cn/2, ite/4, ci/3, can be applied
% RelOp 	  ::=   #= | #\= | #< | #=< | #> | #>=       % i.e., "simple" constraints 
% ConstraintBody  ::=
%         var { X stands for X#=1 }
%	| true | 1
%	| false | 0
%	| var in ConstantRange
%	| element(var,CList,var)  % Not treated
%	| table([VList],CTable)   % Not treated
%	| LinExpr RelOp LinExpr
%	| #\ ConstraintBody
%	| ConstraintBody #/\ ConstraintBody
%	| ConstraintBody #\/ ConstraintBody
%	| ConstraintBody #=> ConstraintBody
%	| ConstraintBody #\ ConstraintBody
%	| ConstraintBody #<=> ConstraintBody 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:-use_module(library(clpfd)).
:-use_module(library(terms)).
:-use_module(library(ordsets)).
:-use_module(library(random)).

:- op(900,    fy, cn).
:- op(740,   xfy, cd).
:- op(750,   xfy, cxd).

:- public cd/2, cd/3, cxd/2, cn/1, cn/2, ite/4, ci/3.
:- dynamic inb/1.
:- multifile clpfd:dispatch_global/4.


clpfd:dispatch_global(cn_ctr(C,L),state, state, Actions) :-
        cn_solve(C,L, Actions).
clpfd:dispatch_global(cd_ctr(C1, C2, L),state, state, Actions) :-
        cd_solve(C1, C2, L, Actions).
clpfd:dispatch_global(cxd_ctr(C1, C2, L),state, state, Actions) :-
        cxd_solve(C1, C2, L, Actions).
clpfd:dispatch_global(cn_ctr3(C,L, ENV),state, state, Actions) :-
        cn_solve3(C,L, ENV, Actions).
clpfd:dispatch_global(cd_ctr3(C1,C2,L,ENV),state, state, Actions) :-
        cd_solve3(C1,C2, L, ENV, Actions).
clpfd:dispatch_global(ite_ctr(C, NC,  C1,  C2, L, ENV),state, state, Actions) :-
        ite_solve(C, NC, C1, C2, L, ENV, Actions).
clpfd:dispatch_global(ci_ctr(C1,  C2, L1, L2, ENV),state, state, Actions) :-
        ci_solve(C1, C2, L1, L2, ENV, Actions).
        

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% cn/1   constructive negation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
cn(C) :-
         term_variables(C, L),
         add_dom(L, DOM),
         clpfd:fd_global(cn_ctr(C,L),state,DOM).  

% no variable in the query (negation as failure = logical negation
cn_solve(true,  _L, Actions) :-  !, Actions = [fail].
cn_solve(1,     _L, Actions) :-  !, Actions = [fail].
cn_solve(false, _L, Actions) :-  !, Actions = [exit].
cn_solve(0,     _L, Actions) :-  !, Actions = [exit].

cn_solve(C,  [], Actions) :-  call(C), !, Actions = [fail].   % no variable (L == [])
cn_solve(_C, [], Actions) :-           !, Actions = [exit].

cn_solve(C, _L, Actions) :-
        gen_ctr_neg(C,NC),    % OK to fail if C is not simple!
        !,
        Actions = [exit, call(user:NC)].

cn_solve(in(V, R),     _L, Actions)  :- !, Actions = [exit, V in \ R].
cn_solve(cn(C),        _L, Actions)  :- !, Actions = [exit, call(user:C)].
cn_solve(cd(C1,C2),    _L, Actions)  :- !, Actions = [exit, call(user:cn(C1)),call(user:cn(C2))].
cn_solve('#\\'(C),     _L, Actions)  :- !, Actions = [exit, call(user:C)].
cn_solve('#\\'(C1,C2), _L, Actions)  :- !, Actions = [exit, call('#<=>'(C1,C2))].  
cn_solve('#/\\'(C1,C2),_L, Actions)  :- !, Actions = [exit, call(user:cd(user:cn(C1),user:cn(C2)))].
cn_solve('#\\/'(C1,C2),_L, Actions)  :- !, Actions = [exit, call(user:cn(C1)),call(user:cn(C2))].
cn_solve('#=>'(C1,C2), _L, Actions)  :- !, Actions = [exit, call(user:C1),call(user:cn(C2))].
cn_solve('#<=>'(C1,C2), _L, Actions) :- !, Actions = [exit, call('#\\'(C1,C2))].

cn_solve(_C, _L, Actions) :-  !, Actions = [].        


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% cd/2   constructive disjunction
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
cd(C1, C2) :-
         term_variables(C1, L1),
         term_variables(C2, L2),
         ord_union(L1,L2,L),
         add_dom(L,DOM),
         clpfd:fd_global(cd_ctr(C1,C2,L),state,DOM).  

% no variable in the query
cd_solve(C1, _C2, [], Actions) :-  call(C1), !, Actions = [exit].
cd_solve(_C1, C2, [], Actions) :-  call(C2), !, Actions = [exit].
cd_solve(_C1,_C2, [], Actions) :-            !, Actions = [fail].

cd_solve(C1, C2, L, Actions) :-   
        \+( (call(C1), assert_bounds(L)) ),
        !,            % C1 = fail
        Actions = [exit, call(user:C2)].

cd_solve(C1, C2, L, Actions) :-   
        \+( (call(C2), assert_bounds(L)) ),
        !,            % C2 = fail
        (retract(inb(_)) -> true),
        Actions = [exit, call(user:C1)].

cd_solve(_C1, _C2, L, Actions) :-
        union_bounds(L, Actions).  % suspend


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% cxd/2   constructive exclusive disjunction
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
cxd(C1, C2) :-
         term_variables(C1, L1),
         term_variables(C2, L2),
         ord_union(L1,L2,L),
         add_dom(L,DOM),
         clpfd:fd_global(cxd_ctr(C1,C2,L),state,DOM).  

cxd_solve(C1, C2, L, Actions) :-   
        \+( (cn(C2),call(C1), assert_bounds(L)) ),
        !,            % C1 = fail
        Actions = [exit, call(user:cn(C1)), call(user:C2)].

cxd_solve(C1, C2, L, Actions) :-   
        \+( (cn(C1), call(C2), assert_bounds(L)) ),
        !,            % C2 = fail
        (retract(inb(_)) -> true),
        Actions = [exit, call(user:cn(C2)), call(user:C1)].

cxd_solve(_C1, _C2, L, Actions) :-
        union_bounds(L, Actions).  % suspend


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% CONSTRAINTS WITH STRATIFIED REASONING %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% cn/2  constructive negation with stratified reasoning (k_flag)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
cn(C, ENV) :-
         term_variables(C, LI),
         remove_var(LI, ENV, L),
         add_dom(L, DOM),
         get_reveil(ENV, Reveil),
         clpfd:fd_global(cn_ctr3(C,L, ENV),state,[max(Reveil)|DOM]).  

% no variable in the query (negation as failure = logical negation
cn_solve3(true,  _L, _ENV, Actions) :-  !, Actions = [fail].
cn_solve3(1,     _L, _ENV, Actions) :-  !, Actions = [fail].
cn_solve3(false, _L, _ENV, Actions) :-  !, Actions = [exit].
cn_solve3(0,     _L, _ENV, Actions) :-  !, Actions = [exit].

cn_solve3(C,  [], _ENV, Actions) :-  call(C), !, Actions = [fail].   % no variable (L == [])
cn_solve3(_C, [], _ENV, Actions) :-           !, Actions = [exit].

cn_solve3(C, _L, _ENV, Actions) :-
        gen_ctr_neg(C,NC),    % OK to fail if C is not simple!
        !,
        Actions = [exit, call(user:NC)].

cn_solve3(_C, _L, ENV, Actions) :-
        test_k(ENV),                    % (K_FLAG == 0 ?)
        !,
        Actions = [].

cn_solve3(in(V, R),       _L, _ENV, Actions)  :- !, Actions = [exit, V in \ R].
cn_solve3(cn(C),          _L, _ENV, Actions)  :- !, Actions = [exit, call(user:C)].
cn_solve3(cn(C, ENV),     _L, ENV,  Actions)  :- !, Actions = [exit, call(user:C)].
cn_solve3(cd(C1,C2),      _L, ENV,  Actions)  :- !, Actions = [exit, call(user:cn(C1,ENV)),call(user:cn(C2,ENV))].
cn_solve3(cd(C1,C2, ENV), _L, ENV,  Actions)  :- !, Actions = [exit, call(user:cn(C1,ENV)),call(user:cn(C2,ENV))].
cn_solve3('#\\'(C),       _L, _ENV, Actions)  :- !, Actions = [exit, call(user:C)].
cn_solve3('#\\'(C1,C2),   _L, _ENV, Actions)  :- !, Actions = [exit, call('#<=>'(C1,C2))].  
cn_solve3('#/\\'(C1,C2),  _L, ENV,  Actions)  :- !, Actions = [exit, call(user:cd(user:cn(C1,ENV),user:cn(C2,ENV), ENV))].
cn_solve3('#\\/'(C1,C2),  _L, ENV,  Actions)  :- !, Actions = [exit, call(user:cn(C1,ENV)),call(user:cn(C2,ENV))].
cn_solve3('#=>'(C1,C2),   _L, ENV,  Actions)  :- !, Actions = [exit, call(user:C1),call(user:cn(C2,ENV))].
cn_solve3('#<=>'(C1,C2),  _L, _ENV, Actions) :- !, Actions = [exit, call('#\\'(C1,C2))].

cn_solve(_C, _L, _ENV, Actions) :-  !, Actions = [].     


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% cd/3   constructive disjunction with stratified reasoning (k_flag)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
cd(C1, C2, ENV) :-
         term_variables(C1, L1),
         term_variables(C2, L2),
         ord_union(L1,L2,LI),
         remove_var(LI, ENV, L),
         get_reveil(ENV, Reveil),
         add_dom(L,DOM),
         clpfd:fd_global(cd_ctr3(C1,C2,L,ENV),state,[max(Reveil)|DOM]).   

% no variable in the query
cd_solve3(C1, _C2, [], _ENV, Actions) :-  call(C1), !, Actions = [exit].
cd_solve3(_C1, C2, [], _ENV, Actions) :-  call(C2), !, Actions = [exit].
cd_solve3(_C1,_C2, [], _ENV, Actions) :-            !, Actions = [fail].

cd_solve3(_C1, _C2, _L, ENV, Actions) :-
        test_k(ENV),                    % (K_FLAG == 0 ?)
        !,
        Actions = [].  

cd_solve3(C1, C2, L, ENV, Actions) :-   
        \+( (decr_k(ENV), call(C1), assert_bounds(L)) ),
        !,            % C1 = fail
        Actions = [exit, call(user:C2)].

cd_solve3(C1, C2, L, ENV, Actions) :-   
        \+( (decr_k(ENV), call(C2), assert_bounds(L)) ),
        !,            % C2 = fail
        (retract(inb(_)) -> true),
        Actions = [exit, call(user:C1)].

cd_solve3(_C1, _C2, L, _ENV, Actions) :-
        !,
        union_bounds(L, Actions).  % suspend


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ite/4
% ite(C,C1,C2,ENV)   Constructive conditional with stratified reasoning (k_flag) -- C must be elementary
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
ite(C, C1, C2, ENV) :-
        term_variables(C, LC),
        term_variables(C1, L1),
        term_variables(C2, L2),
        ord_union(LC, L1, LI),
        ord_union(LI, L2, LII),
        remove_var(LII, ENV, L),
        add_dom(L, DOM),
        get_reveil(ENV,Reveil),
        gen_ctr_neg(C, NC),
        clpfd:fd_global(ite_ctr(C, NC, C1, C2, L, ENV),state,[max(Reveil)|DOM]). 

ite_solve(C, _NC, C1, _C2, [], _ENV, Actions) :-
        call(C),    % no variable in C
        !,
        Actions = [exit,call(user:C1)].

ite_solve(_C, NC, _C1, C2, [], _ENV, Actions) :-
        call(NC),   % can be safely removed for optimization
        !,          % if C failed (where C is ground)
        Actions = [exit,call(user:C2)].

ite_solve(_C, _NC, _C1, _C2, _L, ENV, Actions) :-
        test_k(ENV),                                % (K_FLAG == 0 ?)
        !,
        Actions = [].                              

ite_solve(C, NC, C1, C2, L, ENV, Actions) :-
        \+( (decr_k(ENV), call(NC) ,call(C2), assert_bounds(L)) ),   % Inconsistency test of ELSE part
        !,
        Actions = [exit, call(C), call(C1)].

ite_solve(C, NC, C1, C2, L, ENV, Actions) :-
        \+( (decr_k(ENV), call(C), call(C1), assert_bounds(L)) ),   % Inconsistency test of THEN part
        !,
        (retract(inb(_)) -> true),
        Actions = [exit,  call(NC), call(C2)].

ite_solve(_C, _NC, _C1, _C2, L, _ENV, Actions) :-  
        !,                                    
        union_bounds(L, Actions).  % suspend


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ci/3 Constructive implication with stratified reasoning (k_flag) -- First argument does NOT need to be an elementary constraint
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
ci(C1, C2, ENV) :-
        term_variables(C1, LE1),
        term_variables(C2, LE2),
        remove_var(LE1, ENV, L1),
        remove_var(LE2, ENV, L2),
        ord_union(L1, L2, L),
        add_dom(L, DOM),
        get_reveil(ENV, Reveil),
        clpfd:fd_global(ci_ctr(C1, C2, L1, L2, ENV), state, [max(Reveil)|DOM]). 

ci_solve(C1, C2, [], _L2, _ENV, Actions) :-
        user:C1,    % no variable in C1, C1 is true
        !,
        Actions = [exit,call(user:C2)].
ci_solve(_C1, _C2, [], _L2, _ENV, Actions) :-
        %\+(_C1),    % no variable in C1, C1 is false
        !,
        Actions = [exit].
ci_solve(C1, C2, _L1, [], _ENV, Actions) :-
        \+( user:C2 ),    % no variable in C2, C2 is false
        !,
        Actions = [exit, call(user:C1)].

ci_solve(_C1, _C2, _L1, _L2, ENV, Actions) :-
        test_k(ENV),                                % (K_FLAG == 0 ?)
        !,
        Actions = [].                              

ci_solve(C1, C2, L1, _L2, ENV, Actions) :-
        \+( (decr_k(ENV), user:cn(C1,ENV) ,assert_bounds(L1)) ),   % Inconsistency test 
        !,
        Actions = [exit, call(user:C1), call(user:C2)].

ci_solve(C1, _C2, L1, _L2, ENV, Actions) :-
        \+( (decr_k(ENV), user:C1, assert_bounds(L1)) ),   % Inconsistency test
        !,
        (retract(inb(_)) -> true),
        Actions = [exit, call(user:cn(C1,ENV))].

ci_solve(C1, C2, _L1, L2, ENV, Actions) :-
        \+( (decr_k(ENV), user:cn(C2,ENV) ,assert_bounds(L2)) ),   % Inconsistency test 
        !,
        (retract(inb(_)) -> true),
        (retract(inb(_)) -> true),
        Actions = [exit, call(user:C1), call(user:C2)].

ci_solve(C1, C2, _L1, L2, ENV, Actions) :-
        \+( (decr_k(ENV), user:C2, assert_bounds(L2)) ),   % Inconsistency test
        !,
        (retract(inb(_)) -> true),
        (retract(inb(_)) -> true),
        (retract(inb(_)) -> true),
        Actions = [exit, call(user:cn(C1,ENV))].

ci_solve(_C1, _C2, L1, L2, _ENV, Actions) :-  
        !,
        union_bounds(L1, Actions1),
        union_bounds(L2, Actions2),
        lists:append(Actions1, Actions2, Actions).                       % suspend


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% UTILS %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
assert_bounds(L) :-
%        write(L),nl,
        c_bounds(L, LBV),
        asserta(inb(LBV)).

c_bounds([], []):-!.
c_bounds([X|L], [in(Min,Max,R)|LBV]):-
        fd_min(X, Min),
        fd_max(X, Max),
        fd_dom(X, R),
        c_bounds(L, LBV).


union_bounds(L, Actions) :-
        (retract(inb(LBV1)) -> true),
        (retract(inb(LBV2)) -> true),
        union_bounds_rec(L, LBV1, LBV2, Actions).

union_bounds_rec([], [], [], []):-!.
%% *** Interval union (a.k.a., Meet over the Interval abstract domain) ***
%union_bounds_rec([X|Xs], [inb(Min1, Max1, _)|L1s], [inb(Min2,Max2, _)|L2s], [X in Min..Max|As]):-   % Interval union
%        Min is min(Min1,Min2),
%        Max is max(Max1,Max2),
%        union_bounds_rec(Xs, L1s, L2s, As).
%% *** Union with bounds approximations (non-monotonic, loose information that has been computed) ***
%union_bounds_rec([X|Xs], [inb(Min1, Max1, _)|L1s], [inb(Min2,Max2, _)|L2s], [X in (Min1..Max1)\/(Min2..Max2)|As]):-   % Domain union
%        union_bounds_rec(Xs, L1s, L2s, As).
%% *** Domain union ***
union_bounds_rec([X|Xs], [in(_Min1, _Max1, R1)|L1s], [in(_Min2, _Max2, R2)|L2s], [X in R1 \/ R2|As]):-   % Domain union
        union_bounds_rec(Xs, L1s, L2s, As).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% add_dom(+Xs,-S) vrai ssi Xs est une liste de variable a domaine finie et,
%                          S une liste de condition de reveil portant sur ces variables.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
add_dom([],[]):-!.
add_dom([X|Xs],[dom(X)|S]) :-
        var(X),
        !,
        add_dom(Xs,S).
add_dom([_X|Xs],S) :-
        !,
        add_dom(Xs,S).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% gen_ctr_neg(+E,-NEG)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
gen_ctr_neg(E, NEG) :-
        E =.. [OP|A],
        neg_op(OP,NEGOP),
        NEG =.. [NEGOP|A].
neg_op('#=','#\\=').
neg_op('#>','#=<').
neg_op('#>=','#<').
neg_op('#\\=','#=').
neg_op('#<','#>=').
neg_op('#=<','#>').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% init_env(-ENV)     Environment initialization (K = 1 par defaut)
% init_env(-ENV,+K)  K is the awakening parameter, K needs to be a positive integer
%                    !warning: 2 distinct environments will work on the same constraint store
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
init_env(ENV) :-
        ENV = env(K_FLAG,REVEIL),
        REVEIL in 0..2,
        K_FLAG in 0..2 .

init_env(ENV, K):-
        ENV = env(K_FLAG,REVEIL),
        REVEIL in 0..2,
        K_FLAG in 0..K .

init_env(ENV, K, R):-
        ENV = env(K_FLAG,REVEIL),
        REVEIL in 0..R,
        K_FLAG in 0..K .


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% end_env(+ENV)   Predicate used to close the constraint system
%  ex :   ?- init_env(_ENV,10), end_env(_ENV).
%                _ENV = env(1,10) 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
end_env(ENV) :-
        ENV = env(_, REVEIL),
        nonvar(REVEIL),
        !.
end_env(ENV) :-
        ENV = env(_, REVEIL),
        clpfd:fd_max(REVEIL,R),
        R1 is R - 1,
        REVEIL in 0..R1,
        !,
        end_env(ENV).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% remove_var(L, ENV, LI)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
remove_var(L1, ENV, L2) :-
        term_variables(ENV, L),
        remove_var1(L1, L, L2).

remove_var1([], _L, []):-!.
remove_var1(L1, [], L1):-!.
remove_var1([X|Xs], L, Ys) :-
        mymember_var(X, L, Q),
        !,
        remove_var1(Xs, Q, Ys). 
remove_var1([X|Xs], L, [X|Ys]) :-
        !,
        remove_var1(Xs, L, Ys).

mymember_var(_X, [], _) :- !, fail.
mymember_var(X, [Y|Ys], Ys) :-
        X == Y,
        !.
mymember_var(X, [Y|Ys], [Y|Zs]) :-
        X \== Y,
        !,
        mymember_var(X, Ys, Zs).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% decr_k(+ENV) decreases k
% ex : init_env(_ENV,10),decr_k(_ENV).
%           _ENV = env(_A,10)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
decr_k(ENV):-
        ENV = env(K_FLAG,_Reveil),
        clpfd:fd_max(K_FLAG,K),
        NK is K - 1,
        K_FLAG in 0..NK .


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% test_k(+ENV). true iff K_FLAG == 0.
% ex : init_env(ENV,5),decr_k(ENV),test_k(ENV).   -- no
% ex : init_env(ENV,1),decr_k(ENV),test_k(ENV).   -- ENV = env(_A,0) 
% ex : init_env(ENV),test_k(ENV).                 -- no        
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
test_k(ENV):-
        ENV = env(K_FLAG,_Reveil),
        clpfd:fd_max(K_FLAG,K),
        K == 0.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% get_reveil(+ENV,-Reveil). 
% ex : init_env(ENV,10), get_reveil(ENV,Reveil) .       -- ENV = env(Reveil,10) 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
get_reveil(ENV, Reveil) :-
        ENV = env(_, Reveil).
