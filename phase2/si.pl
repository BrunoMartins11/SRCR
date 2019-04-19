:- dynamic '-'/1.
:- op(995, fx, '@|').  % operador de negacao
:- op(996, xfy, '@&').  % operador de conjuncao
:- op(997, xfy, '@$').  % operador de disjuncao
:- op(997, xfy, '@#').  % operador de negacao exclusiva
:- op(998, xfx, '@=>' ).  % operador de implicacao
:- op(999, xfx, '@<=>'). % operador de equivalencia


nao(Questao) :- Questao, !, fail.
nao(_).

si(P0 @<=> P1, V) :-
                  si(P0, V0),
                  si(P1, V1),
                  equivalencia(V0, V1, V).
si(P0 @=> P1, V) :-
                 si(P0, V0),
                 si(P1, V1),
                 implicacao(V0, V1, V).
si(P0 @$ P1, V) :-
                 si(P0, V0),
                 si(P1, V1),
                 disjuncao(V0, V1, V).
si(P0 @& P1, V) :-
                 si(P0, V0),
                 si(P1, V1),
                 conjuncao(V0, V1, V).

si(P0 @# P1, V) :-
                  si(P0, V0),
                  si(P1, V1),
                  negacaoExclusiva(V0, V1, V).

si(@| P0, V) :- si(P0, P1), negacao(P1, V).
si(P, verdadeiro) :- P.
si(P, falso) :- -P.
si(P, desconhecido) :-
                     nao(P),
                     nao(-P).

equivalencia(Y, Y, verdadeiro) :- Y \= desconhecido.
equivalencia(desconhecido, _, desconhecido).
equivalencia(_, desconhecido, desconhecido).
equivalencia(verdadeiro, falso, falso).
equivalencia(falso, verdadeiro, falso).

implicacao(verdadeiro, Y, Y).
implicacao(falso, _, verdadeiro).
implicacao(desconhecido, Y, Y) :- Y \= falso.
implicacao(desconhecido, falso, desconhecido).

disjuncao(verdadeiro, _, verdadeiro).
disjuncao(falso, Y, Y).
disjuncao(desconhecido, Y, desconhecido) :- Y \= verdadeiro.
disjuncao(desconhecido, verdadeiro, verdadeiro).

conjuncao(verdadeiro, Y, Y).
conjuncao(falso, _, falso).
conjuncao(desconhecido, falso, falso).
conjuncao(desconhecido, Y, desconhecido) :- Y \= falso.

negacao(verdadeiro, falso).
negacao(falso, verdadeiro).
negacao(desconhecido, desconhecido).

negacaoExclusiva(P, Q, R) :-
                           conjuncao(P, Q, R0), negacao(R0, R1),
                           disjuncao(P, Q, R2),
                           conjuncao(R1, R2, R).

