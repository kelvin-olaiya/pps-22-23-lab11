% search2 (Elem , List )
search2(E, [E, E | T]) :- !.
search2(E, [_|T]) :- search2(E, T).

% looks for two consecutive occurrences of Elem
search_two(E, [E, X, E | T]) :- X \= E, !.
search_two(E, [_|T]) :- search2(E, T).

% size (List , Size)
% Size will contain the number of elements in List | Fully Relational.
size([], 0).
size([_ | T], N) :- size(T, N2), N is N2 + 1.

% sum(List , Sum)
sum([], 0).
sum([H | T], N) :- sum(T, N2), N is N2 + H.

% max(List, Max, Min)
% Max is the biggest element in List
% Min is the smallest element in List
% Suppose the list has at least one element
greatest(A, B, X) :- A > B, !, X = A.
greatest(A, B, B). 

lowest(A, B, X) :- greatest(A, B, B), !, X = A.
lowest(A, B, B).

max([H | T], RMax, RMin) :- max(T, H, H, RMax, RMin).
max([], Max, Min, Max, Min).
max([H|T], Max, Min, RMax, RMin) :- greatest(H, Max, G), lowest(H, Min, L), max(T, G, L, RMax, RMin).

%sublist(List1, List2)
sublist([], _).
sublist([H|T], L) :- member(H, L), sublist(T, L).

% dropAny
dropAny(X, [X | T], T).
dropAny(X, [H | Xs], [H | L]) :- dropAny(X, Xs, L).

% dropFirst
dropFirst(X, [X | T], T) :- !.
dropFirst(X, [H | Xs], [H | L]) :- dropFirst(X, Xs, L).

%dropLast
dropLast(X, [H | Xs], [H | L]) :- dropLast(X, Xs, L), !.
dropLast(X, [X | T], T) :- !.

%dropAll
dropAll(X, [], []).
dropAll(X, [H | T], R) :- copy_term(X, H), !,  dropAll(X, T, R).
dropAll(X, [H | T], [H | R]) :- dropAll(X, T, R).
 

%%%--------%%%
%%% GRAPHS %%%
%%%--------%%%

%fromList
fromList([_], []).
fromList([H1,H2|T],[e(H1,H2)|L]) :- fromList([H2|T], L).

%fromCircList
fromCircList([H|T], G) :- fromList([H|T], G1), reverse([H|T], [H2|_]), append(G1, [e(H2,H)], G).

%outDegree
outDegree([], _, 0).
outDegree([e(N, _) | T], N, O) :- outDegree(T, N, O2), O is O2 + 1, !.
outDegree([H | T], N, O) :- outDegree(T, N, O).

%dropNode
dropNode(G, N, OG) :- dropAll(e(N, _), G, G2), dropAll(e(_, N), G2, OG).

%reaching
reaching(G, N, L) :- findall(X, member(e(N,X), G), L).  

distinct_append(X, L, L) :- member(X, L), !.
distinct_append(X, L, R) :- append(L, [X], R).

distinct_prepend(X, L, L) :- member(X, L), !.
distinct_prepend(X, L, [X | L]). 

%nodes
nodes([], []).
nodes([e(F, S) | T], N) :- nodes(T, N1), distinct_prepend(S, N1, N2), distinct_prepend(F, N2, N).

% anypath
anypath(G, N1, N2, [e(N1, N2)]) :- member(e(N1, N2), G).
anypath(G, N1, N2, [e(N1, X)|P]) :- reaching(G, N1, L), member(X, L), anypath(G, X, N2, P).

% distinct
distinct([], []).
distinct([H|T], R) :- member(H, T), distinct(T, R), !.
distinct([H|T], [H|R]) :- distinct(T, R).

% allreaching
allreaching(G, N, L) :- findall(X, anypath(G, N, X, _), R), distinct(R, L).

%%%----------------%%%
%%% GRID-LIKE NETS %%%
%%%----------------%%%


interval(A, B, A).
interval(A, B, X) :- A2 is A + 1, A2 < B, interval(A2, B, X).

neighbour(e((A, B), (A, B2))) :- B2 is B+1.
neighbour(e((A, B), (A2, B))) :- A2 is A+1.
neighbour(e((A, B), (A2, B2))) :- A2 is A+1, B2 is B-1. %% In term of node reachability, this is additional
neighbour(e((A, B), (A2, B2))) :- A2 is A+1, B2 is B+1. %% same

graphlink(N, M, e((X, Y), (X2, Y2))) :-
		interval(0, N, X),
		interval(0, M, Y),
		neighbour(e((X, Y), (X2, Y2))),
		X2 >= 0, Y2 >= 0, X2 < N, Y2 < M.

grid(N, M, G) :- findall(X, graphlink(N, M, X), G).

anypathL(G, N1, N2, L, R) :- anypath(G, N1, N2, R), length(R, N), N < L.

%%%----------%%%
%%% Connect3 %%%
%%%----------%%%

% next(@Table, @Player, -Result, -NewTable)
% Table is a representation of a TTT table where players x or o are playing
% Player (either x or o) is the player to move
% Result is either win(x), win(o), nothing, or even
% NewTable is the table after a valid move
% Should find a representation for the Table
% Calling the predicate should give all results

% Table representation:  [[_,_,_],[x,o,x],[o,x,o]]
% ------------------------------------------------------
placed(X) :- X == o.
placed(X) :- X == x.
free(X) :- X \== o, X \== x.

% R: row, P: player
left([P, _, _], P) :- placed(P). 
middle([_, P, _], P) :- placed(P).
right([_, _, P], P) :- placed(P).

same(X, Y, Z) :- X == Y, Y == Z.

result([U, M, B], win(X)) :- left(U, X), left(M, Y), left(B, Z), same(X, Y, Z), !. 
result([U, M, B], win(X)) :- middle(U, X), middle(M, Y), middle(B, Z), same(X, Y, Z),!.
result([U, M, B], win(X)) :- right(U, X), right(M, Y), right(B, Z), same(X, Y, Z),!.

result([U, M, B], win(X)) :- left(B, X), middle(B, Y), right(B, Z), same(X, Y, Z),!.
result([U, M, B], win(X)) :- left(M, X), middle(M, Y), right(M, Z), same(X, Y, Z),!.
result([U, M, B], win(X)) :- left(U, X), middle(U, Y), right(U, Z), same(X, Y, Z),!.

result([U, M, B], win(X)) :- right(U, X), middle(M, Y), left(B, Z), same(X, Y, Z),!.
result([U, M, B], win(X)) :- left(U, X), middle(M, Y), right(B, Z), same(X, Y, Z),!.

full([A, B, C]) :- placed(A), placed(B), placed(C).
result([U, M, B], even) :- full(U), full(M), full(B), !.
result(T, nothing). 

next([A, B, C], P, [P, B, C]) :- atom(A), free(A).
next([A, B, C], P, [A, P, C]) :- atom(B), free(B).
next([A, B, C], P, [A, B, P]) :- atom(C), free(C).

next([[A, B, C], [D, E, F]], P, [P, B, C]) :- placed(D), free(A).
next([[A, B, C], [D, E, F]], P, [A, P, C]) :- placed(E), free(B).
next([[A, B, C], [D, E, F]], P, [A, B, P]) :- placed(F), free(C). 

% U: Upper, M: Middle, B: bottom
next([U, M, B], P, R, [U, M, N]) :- next(B, P, N), result([U, M, N], R).
next([U, M, B], P, R, [U, N, B]) :- next([M, B], P, N), result([U, N, B], R).
next([U, M, B], P, R, [N, M, B]) :- next([U, M], P, N), result([N, M, B], R). 

% game(@Table,@Player,-Result,-TableList)
% TableList is the sequence of tables until Result win(x), win(o) or even
other(X, o) :- X == x.
other(X, x) :- X == o.

game(T, P, win(X), [T]) :- placed(X), !.
game(T, P, even, [T]) :- result(T, even).

game(T, P, R, [N|L]) :- next(T, P, R, N), other(P, X), game(N, X, R, L).

