% Definições iniciais
:- dynamic utente/4.
% -------------------------------------------------------
% --------------- Predicados auxiliares -----------------
% -------------------------------------------------------

% Extensao do predicado nao: Q -> {V,F}
nao(Q) :- Q, !, fail.
nao(_).

% Extensao do predicado solucoes: F, Q, S -> {V,F}
solucoes(F,Q,_) :- Q, assert(tmp(F)), fail.
solucoes(_,_,S) :- construir(S, []).

% Extensao do predicado construir: S1,S2 -> {V,F}
construir(S1, S2) :- retract(tmp(X)), !, construir(S1, [X|S2]).
construir(S,S).

%--------------------------------------------------------
%----------------- Predicados ---------------------------
%--------------------------------------------------------
utente( 0, 'Jose',     55, 'Rua dos Zecas').
utente( 1, 'Joao',     21, 'Rua de Baixo').
utente( 2, 'Manuel',   36, 'Rua Maria Albertina').
utente( 3, 'Carlos',   43, 'Rua da Fabrica').
utente( 4, 'Maria',    73, 'Avenida Camoes').

% Registo de utentes

add_utente(Id, Nome, Idade, Cidade) :-  nao(utente(Id, _, _ ,_)), Idade >= 0, Id >= 0,
                                        assert(utente(Id, Nome, Idade, Cidade)).

remove_utente(Id) :- retract(utente(Id, _, _, _)).
