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

<<<<<<< HEAD
<<<<<<< HEAD
lista_soma([], 0).
lista_soma([Head | T], R) :-
                          lista_soma(T, R0),
                          R is Head + R0.

% Extensao do predicado comprimento: L, R -> {V,F}
comprimento([], 0).
comprimento([_ | T], R) :-
                         comprimento(T, R0),
                         R is R0 + 1.

% Extensao do predicado data: D, M, A -> {V,F}
data(D, M, _) :-
               pertence(M, [1,3,5,7,8,10,12]),
               D >= 1,
               D =< 31.
data(D, M, _) :-
               pertence(M, [4,6,9,11]),
               D >= 1,
               D =< 30.
data(D, 2, A) :-
               A mod 4 =\= 0, % ano nao bissexto
               D >= 1,
               D =< 28.
data(D, 2, A) :-
               A mod 4 =:= 0,
               D >= 1,
               D =< 29.
=======
=======
>>>>>>> fb60cfb2d4293480177d445157d383ac725dbe79
% Extensao do predicado append: L1, L2, L3 -> {V,F}
append([], List, List).
append([Head|Tail], List, [Head|Rest]) :-
append(Tail, List, Rest).
                                
<<<<<<< HEAD
>>>>>>> 599f8f6... almost done
=======
>>>>>>> fb60cfb2d4293480177d445157d383ac725dbe79
