% Predicados auxiliares
%
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

list_sum( [],0 ).
list_sum( [Head | Tail], T) :-
                                list_sum(Tail, SUM),
                                T is Head + SUM.

% Extensao do predicado comprimento: L, R -> {V,F}
comprimento([], 0).
comprimento([_ | T], R) :-
                         comprimento(T,R0),
                         R is R0 + 1.
