% -------------------------------------------------------
% --------------- Predicados auxiliares -----------------
% -------------------------------------------------------

% Extensao do predicado nao: Q -> {V,F}
nao(Q) :- Q, !, fail.
nao(_).

% Extensao do predicado solucoes: F, Q, S -> {V,F}
solucoes(F, Q, _) :- Q, assert(tmp(F)), fail.
solucoes(_, _, S) :- construir(S, []).

% Extensao do predicado construir: S1,S2 -> {V,F}
construir(S1, S2) :- retract(tmp(X)), !, construir(S1, [X | S2]).
construir(S,S).

% Extensao do predicado pertence: Elemento, Lista: -> {V,F}
pertence(H, [H | _]).
pertence(X, [H | T]) :-
                      X \= H,
                      pertence(X, T).

% Extensao do predicado unicos: L1, L2 -> {V,F}
unicos([], []).
unicos([H | T], R) :-
                    pertence(H, T),
                    unicos(T, R).
unicos([H | T], [H | R]) :-
                          nao(pertence(H, T)),
                          unicos(T, R).

% Extensao do predicado lista_pares_fst: L1, L2 -> {V,F}
lista_pares_fst([], []).
lista_pares_fst([(A, _) | T], R) :-
                                  lista_pares_fst(T, L),
                                  append([A], L, R).

% Extensao do predicado append: L1, L2, L3 -> {V,F}
append([], List, List).
append([Head|Tail], List, [Head|Rest]) :-
append(Tail, List, Rest).
                                
