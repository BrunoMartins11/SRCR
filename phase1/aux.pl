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

% Extensao do predicado soma: Lista, Valor -> {V,F}
soma([],0).
soma([N|Ns], T) :- soma(Ns,X), T is X+N.

% Extençao do predicado media: Lista, Valor -> {V,F}
media([],0).
media(List,Med) :-
    soma(List,X),
    comprimento(List,L),
    Med is (div(X,L)).

%Extesao do predicado mais_rep: L, M -> {V,F}
highest((X1,Y1),(_,Y2),(X1,Y1)):- Y1 >= Y2.
highest((_,Y1),(X2,Y2),(X2,Y2)):- Y2 > Y1.

maxR([X],X).
maxR([X|Xs],K):- maxR(Xs,Z),highest(X,Z,K).

rep([],R,R).
rep([X|Xs],R,R1):-modify(R,X,R2),rep(Xs,R2,R1).

maxRepeated(X,R):- rep(X,[],K),maxR(K,R).
modify([],X,[(X,1)]).
modify([(X,Y)|Xs],X,[(X,K)|Xs]):- K is Y+1.
modify([(Z,Y)|Xs],X,[(Z,Y)|K]):- Z \= X, modify(Xs,X,K).
