% Definições iniciais
:- op(900, xfy, '::').

% -------------------------------------------------------
% --------------- Predicados auxiliares -----------------
% -------------------------------------------------------

% Extensao do predicado nao: Q -> {V,F}
nao(Q) :- Q, !, fail.
nao(Q).

% Extensao do predicado solucoes: F, Q, S -> {V,F}
solucoes(F,Q,S) :- Q, assert(tmp(F)), fail.
solucoes(F,Q,S) :- construir(S, []).

% Extensao do predicado construir: S1,S2 -> {V,F}
construir(S1, S2) :- retract(tmp(X)), !, construir(S1, [X|S2]).
construir(S,S).
