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

utente( 0, 'Jose',     55, 'Rua dos Zecas').
utente( 1, 'Joao',     21, 'Rua de Baixo').
utente( 2, 'Manuel',   36, 'Rua Maria Albertina').
utente( 3, 'Carlos',   43, 'Rua da Fabrica').
utente( 4, 'Maria',    73, 'Avenida Camoes').

% Registo de utentes

add_utente(Id, Nome, Idade, Cidade) :- \+ utente(Id, Nome, Idade, Cidade), Idade >= 0, Id >= 0,
                                        assertz(utente(Id, Nome, Idade, Cidade)).

remove_utente(Id, _, _, _) :- retract(utente(Id, _, _, _)).

