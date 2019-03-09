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

% Extensao do predicado pertence: Elemento, Lista: -> {V,F}
pertence(H,[H|_]).
pertence(X,[H|T]) :-
                   X \= H,
                   pertence(X,T).

% Extensao do predicado unicos: L1, L2 -> {V,F}
unicos([],[]).
unicos([H|T], R) :-
                  pertence(H,T),
                  unicos(T,R).
unicos([H|T], [H|R]) :-
                      nao(pertence(H,T)),
                      unicos(T,R).

% Extensao do predicado lista_pares_fst: L1, L2 -> {V,F}
lista_pares_fst([], []).
lista_pares_fst([(A, _) | T], R) :-
                                  lista_pares_fst(T, L),
                                  append([A], L, R).


%--------------------------------------------------------
%----------------- Predicados ---------------------------
%--------------------------------------------------------

% Extensao do predicado utente: IdUt, Nome, Idade, Cidade -> {V,F}
utente(0,     'Jose', 55,     'Porto').
utente(1,     'Joao', 21,     'Braga').
utente(2,   'Manuel', 36,     'Porto').
utente(3,   'Carlos', 43, 'Guimaraes').
utente(4,    'Maria', 73, 'Guimaraes').
utente(5,    'Joana',  8,     'Porto').
utente(6, 'Fernando', 49,    'Aveiro').
utente(7,     'Joao', 29,    'Aveiro').
utente(8,      'Ana', 40,     'Braga').
utente(9, 'Catarina', 17,     'Braga').

% Extensao do predicado servico: IdServ, Descricao, Instituicao, Cidade -> {V,F}
servico(0,      'Cirurgia',    'Hospital Privado de Braga',     'Braga').
servico(1,  'Dermatologia',    'Hospital Privado de Braga',     'Braga').
servico(2,     'Pediatria',    'Hospital Privado de Braga',     'Braga').
servico(3,   'Pneumologia',            'Hospital de Braga',     'Braga').
servico(4,  'Reumatologia',            'Hospital de Braga',     'Braga').
servico(5,  'Dermatologia',        'Hospital de Guimaraes', 'Guimaraes').
servico(6,     'Pediatria',        'Hospital de Guimaraes', 'Guimaraes').
servico(7,   'Psiquiatria',        'Hospital de Guimaraes', 'Guimaraes').
servico(8,   'Cardiologia', 'Hospital da Luz de Guimaraes', 'Guimaraes').
servico(9, 'Oftalmologia', 'Hospital da Luz de Guimaraes',  'Guimaraes').
servico(10,  'Cardiologia',           'Hospital de S.Joao',     'Porto').
servico(11,     'Cirurgia',           'Hospital de S.Joao',     'Porto').
servico(12,    'Ortopedia',           'Hospital de S.Joao',     'Porto').
servico(13,    'Pediatria',           'Hospital de S.Joao',     'Porto').
servico(14,  'Pneumologia',           'Hospital de S.Joao',     'Porto').


% Extensao do predicado add_utente: IdUt, Nome, Idade, Cidade -> {V,F}
add_utente(Id, Nome, Idade, Cidade) :-
                                     nao(utente(Id, _, _ ,_)),
                                     Idade >= 0,
                                     Id >= 0,
                                     assert(utente(Id, Nome, Idade, Cidade)).

% Extensao do predicado remove_utente: IdUt -> {V,F}
remove_utente(Id) :- retract(utente(Id, _, _, _)).

% Extensao do predicado instituicoes: R -> {V,F}
instituicoes(R):-
                solucoes(I, servico(_, _, I, _), L),
                unicos(L, R).

% Extensao do predicado instituicoes_cidade: Cidade, R -> {V,F}
instituicoes_cidade(C, R) :-
                           solucoes((I, C), servico(_, _, I, C), L0),
                           unicos(L0, L),
                           lista_pares_fst(L, R).
