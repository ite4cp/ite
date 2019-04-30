%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% test_ite.pl - Author: Arnaud Gotlieb   (2018/06/20)  - SIMULA RESEARCH LABORATORY
%
% Test file for testing ITE
% ?- run_tests.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- use_module(library(plunit)).
:- ensure_loaded([ite]).

:- begin_tests(ite).

test(cn1) :-
        X in 4..15, Y in 0..10, cn(X #> Y-3 #/\ X #> Y+1),
        fd_dom(X, 4..11), fd_dom(Y,3..10).
test(cn2) :-
        X in 0..10, cn((X #= 0) cd (Y #= 4) cd (X #= 9)),
        fd_dom(X, (1..8)\/{10}), fd_dom(Y,(inf..3)\/(5..sup)).
test(cn3) :-
        X in 0..10, cn((X #= 0) cd (Y #= 4) cd (X #= 9)), cn((Y #= 9) cd (Y #= 6) cd (Y #= 7)),
        fd_dom(X, (1..8)\/{10}), fd_dom(Y,(inf..3)\/{5}\/{8}\/(10..sup)).
test(cn4) :-
        X in 0..10, cn(cd(X #= 0, X #= 4) #\/ cd(X #= 1, X #= 7)),
        fd_dom(X, (2..3)\/(5..6)\/(8..10)).
test(cn5) :-
        cn(X in(2..3)\/(5..6)\/(8..10)),
        fd_dom(X, (inf..1)\/{4}\/{7}\/(11..sup)).


test(cd1) :-
        X in 4..5, Y in 0..1, Z in 2..9, T in 4..5, (X + Y #= Z) cd (X + T #= Z),
        fd_dom(X, 4..5), fd_dom(Y, 0..1), fd_dom(T, 4..5), fd_dom(Z,  (4..6) \/ (8..9) ).
test(cd2) :-
        X in 4..5, Y in 0..1, Z in 2..9, T in 4..5, (X + Y #= Z) cd (X + T #= 0),
        fd_dom(X, 4..5), fd_dom(Y, 0..1), fd_dom(T, 4..5), fd_dom(Z, 4..6).
test(cd3, [fail]) :-
        X in 4..5, Y in 0..1, Z in 2..9, T in 4..5, ((X + Y #= 0) cd (X + T #= 0) cd (Z + T #= 0)).
test(cd4) :-
        (X #= 0) cd (X #= 4),
        fd_dom( X, {0}\/{4}). 
test(cd5) :-
        (X #= 0) cd (X #= 4) cd (X #= 9),
       fd_dom(X,{0}\/{4}\/{9}). 
test(cd6):-
        (X #= 0) cd (X #= 4) cd (X #= 9), (X #= 9) cd (X #= 4) cd (X #= 7),
        fd_dom(X, {4}\/{9}). 
test(cd7) :-
        (X #= 0) cd (Y #= 4) cd (X #= 9), (X #= 9) cd (Y #= 4) cd (Y #= 7),
        fd_dom(X,inf..sup), fd_dom(Y,inf..sup).
test(cd8) :-
        (X #= 0) cd (Y #= 4) cd (X #= 9), (Y #= 9) cd (Y #= 6) cd (Y #= 7),
        fd_dom(X, {0}\/{9}),  fd_dom(Y, (6..7)\/{9}).
test(cd9) :-
        A in 1..10, B in 1..10, (A+7 #=< B) cd (B+7 #=< A), % Ex. "Constructive Disjunction revisited" 1996, Wurtz, Muller
        fd_dom(A, (1..3)\/(8..10)), fd_dom(B, (1..3)\/(8..10)).
test(cd10) :-
        A in 1..5, B in 1..5, (A-B #= 4) cd (B-A #= 4),
        fd_dom(A, {1}\/{5}), fd_dom(B, {1}\/{5}).
test(cd11) :-
        X #> 3, Y in 0..9,  (X + 2 #< Y) cd (X #=< 2),
        fd_dom(X, 4..6), fd_dom(Y, 7..9).
test(cd12):-
        A in 1..10, B in 1..10, (A+7 #=< B) cd (cn(B+7 #> A)), (A #> 1,B #<9) cd (A #> 2, A#<10),
        fd_dom(A, {3}\/(8..10)), fd_dom(B, (1..3)\/{10}).
test(cd13) :-
        A in 1..10, B in 1..10, (A+7 #=< B) #\/ (#\(B+7 #> A)), (A #> 1 #/\B #<9) #\/ (A #> 2 #/\ A#<10),
        fd_dom(A, 1..10), fd_dom(B, 1..10). 
test(cd14):-
        A in 1..10000, B in 1..10000, C in 9000..10000, (A + C #< B) cd (B+C #<A),
        fd_dom(A, (1..999)\/(9002..10000)), fd_dom(B, (1..999)\/(9002..10000)), fd_dom(C, 9000..9998). 
test(cd15):-
        X in -10000000..10000000, Y in -10000000..10000000, X #= Y, (X #= 1)  cd (Y #= 2),
        fd_dom(X, 1..2), fd_dom(Y, 1..2).
test(cd16, [fail]):-
        (X #= 0) cd (X #= 1000) cd (X #= 100000), (X #= 10) cd (X #= 10000) cd (X #= 1000000). 


test(cxd1, [true(X =:= 0), true(Z =:= 0)]):-
        X in 0..3, Y in 4..5, Z in -2..0, (X #= Y) cxd (X #= Z),
        fd_dom(Y, 4..5).
test(cxd2, [fail]):-
        X in 1..3, Y in 4..5, Z in -2..0, (X #= Y) cxd (X #= Z).
test(cxd3) :-
        (X in 0..4 #/\ Y #=2*X) cxd (X in 5..10 #/\ Y #=3*X) cxd (X in 11..100 #/\ Y #= -X*X),
        fd_dom(X, 0..100), fd_dom(Y, (-10000.. -121)\/(0..8)\/(15..30)).

test(cns1) :-
        init_env(ENV, [kflag(2)]), X in 0..10, cn(cd(X #= 0, X #= 4, ENV) #\/ cd(X #= 1, X #= 7, ENV), ENV),
        fd_dom(X, (2..3)\/(5..6)\/(8..10)).



test(cds1) :-
        init_env(ENV,[kflag(7)]), cd(cd(X#=0, Y #= 4, ENV), X #= 9, ENV), cd(cd(Y #= 9, Y #= 6, ENV),Y #= 7, ENV), end_env(ENV),
        fd_dom(X, {0}\/{9}), fd_dom(Y, (6..7)\/{9}).
test(cds2):-
        init_env(ENV,[kflag(6)]),cd(cd(X#=0, X #= 4, ENV), X #= 9, ENV),cd(cd(Y #= 9, Y #= 6, ENV),Y #= 7, ENV), end_env(ENV),
        fd_dom(X, {0}\/{4}\/{9}), fd_dom(Y, (6..7)\/{9}).
test(cds3):-
        init_env(ENV,[kflag(3)]),cd(cd(X#=0, Y #= 4, ENV), X #= 9, ENV),cd(cd(Y #= 9, X #= 6, ENV),Y #= 7, ENV), end_env(ENV),
        fd_dom(X, {0}\/{6}\/{9}),fd_dom(Y, {4}\/{7}\/{9}).
test(cds4, [fail]):-
        init_env(ENV,[kflag(1)]), cd(X#=0, X #= 4, ENV), cd(X #= 9, X#=4, ENV), cd(X #= 9, X #= 0, ENV),end_env(ENV).
test(cds5, [true(X=:=4)]) :-
        init_env(ENV,[kflag(1)]), cd(X#=0, X #= 4, ENV), cd(X #= 9, X#=4, ENV), cd(X #= 9, X #= 4, ENV),end_env(ENV).
test(cds6, [true(X =:= 4)]):-
        init_env(ENV,[kflag(1)]), cd(X#=0, X #= 4, ENV), cd(X #= 9, X#=4, ENV), cd(X #= 4, X #= 0, ENV),end_env(ENV).



test(ite1, [true(I0 =:= 0)]):-
        init_env(_ENV), J0 in 0..6, ite(I0 #= 0, J2 #= J0-1 , J2 #= J0, _ENV), I0 #= 0, end_env(_ENV),
        fd_dom(J0, 0..6), fd_dom(J2, -1..5).
test(ite2, [true(I0 =:= 1)]) :-
        init_env(_ENV), J0 in 0..6, ite(I0 #= 0, J2 #= J0-1 , J2 #= J0, _ENV), I0 #= 1, end_env(_ENV),
        fd_dom(J2, 0..6), fd_dom(J0, 0..6).
test(ite3, [true(J0 =:= 2)]):-
        init_env(ENV), ite(I0 #=< 16, J2 #= J0*I0, J2 #= J0, ENV), J2 #> 8, J0 #= 2, end_env(ENV),
        fd_dom(I0, 5..16), fd_dom(J2, 10..32).
test(ite4):-
        init_env(ENV), ite(I0 #=< 16, J #= 1, J #= 5, ENV), end_env(ENV),
        fd_dom(I0, inf..sup), fd_dom(J, {1}\/{5}).

test(ite5, [true(J =:= 5)]):-
        init_env(ENV), ite(I0 #=< 16, J #= 1, J #= 5, ENV), J #> 3, end_env(ENV),
        fd_dom(I0, 17..sup).

test(ci1):-
        init_env(_ENV), ci(X #=< 7, Y #< 5, _ENV), ci(Y #>= 5, X #= 4, _ENV), X #< Y, end_env(_ENV),
        fd_dom(X, inf..3),
        fd_dom(Y, inf..4).

test(opts1):-
        init_env(E, []), init_env(E, [dmin(0), dmax(100), kflag(10)]), init_env(E, [reveil(3), kflag(0), dmax(99)]), cd(X#=1, X#=6, E),
        end_env(E),end_env(E),
        fd_dom(X, inf..99).

test(complex1):-
        cd(cd(X#=0, Y #= 4), X #= 9), cd(cd(Y #= 9, Y #= 6),Y #= 7),
        fd_dom(X, {0}\/{9}), fd_dom(Y, (6..7)\/{9}).

test(complex2):-
        init_env(ENV,[kflag(7)]), cd(cd(X#=0, Y #= 4, ENV), X #= 9, ENV), cd(cd(Y #= 9, Y #= 6, ENV),Y #= 7, ENV), end_env(ENV),
        fd_dom(X, {0}\/{9}), fd_dom(Y, (6..7)\/{9}).

test(complex3) :-  %smt(Y in 30..40 #\/ Y #=X #\/ X*2 #=Y), X in 0..10.   --> Y in inf..sup, X in 0..10 
        init_env(ENV, [kflag(5)]), cd(cd(Y in 30..40, Y#=X, ENV), X*2 #=Y, ENV), X in 0..10,end_env(ENV),
        fd_dom(X, 0..10), fd_dom(Y, (0..20)\/(30..40)).

test(complex4):- %smt(Y in 1..100 #\/ Y#=X #\/ X #=Y), X in 0..10.   --> Y in inf..sup, X in 0..10
        init_env(ENV, [kflag(5)]), cd(cd(Y in 1..100, Y#=X, ENV), X #=Y, ENV), X in 0..10, end_env(ENV),
        fd_dom(X, 0..10), fd_dom(Y, 0..100).

test(complex5) :-   %smt(X #= 1 #\/ X#=3 #\/ X*X #=100). --> no
        init_env(ENV, [kflag(5)]), cd(cd(X #= 1, X #= 3, ENV), X*X #= 100, ENV),end_env(ENV),
        fd_dom(X,{-10}\/{1}\/{3}\/{10}).

test(complex6) :-
        cd(cd(X in 0..9 #/\ Y #= X*X, X in 9..90 #/\ Y #= 90 - X), X in 90..100 #/\ Y - 8100 #= X*X),
        fd_dom(X, 0..100), fd_dom(Y, (0..81)\/(16200..18100)).
        
        
test(complex7, [true(Y=:=3), true(Z=:=3)]):-   % ultrametric Moore and Prosser JAIR 32 (2008) 901-938
        init_env(ENV, [kflag(5)]), cd(cd(X #> Y #/\ Y #= Z, Y #> X #/\ X #= Z, ENV), cd(Z #> X #/\ X #=Y, X #= Y #/\ Y #= Z, ENV), ENV), X in 5..100, Y in 3..100, Z in -100..3, end_env(ENV),
        fd_dom(X, 5..100).

test(complex8, [fail]) :-
          X in 1..10000, Y in 1..10000, Z in 1..10000, C in 4..7,(X-Y #= C) cd (Y-X #= C),  (X-Z #= C) cd (Z-X #= C),  (Z-Y #= C) cd (Y-Z #= C).

:-end_tests(ite).
