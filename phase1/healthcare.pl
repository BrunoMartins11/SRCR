% Modulo auxiliar
:- consult('aux.pl').

% Definições iniciais
:- op(900, xfy, '::').
:- dynamic utente/4.
:- dynamic servico/4.
:- dynamic cuidado/4.


% Factos
%
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
servico(0,     'Cirurgia',    'Hospital Privado de Braga',     'Braga').
servico(1, 'Dermatologia',    'Hospital Privado de Braga',     'Braga').
servico(2,    'Pediatria',    'Hospital Privado de Braga',     'Braga').
servico(3,  'Pneumologia',            'Hospital de Braga',     'Braga').
servico(4, 'Reumatologia',            'Hospital de Braga',     'Braga').
servico(5, 'Dermatologia',        'Hospital de Guimaraes', 'Guimaraes').
servico(6,    'Pediatria',        'Hospital de Guimaraes', 'Guimaraes').
servico(7,  'Psiquiatria',        'Hospital de Guimaraes', 'Guimaraes').
servico(8,  'Cardiologia', 'Hospital da Luz de Guimaraes', 'Guimaraes').
servico(9, 'Oftalmologia', 'Hospital da Luz de Guimaraes', 'Guimaraes').
servico(10, 'Cardiologia',           'Hospital de S.Joao',     'Porto').
servico(11,    'Cirurgia',           'Hospital de S.Joao',     'Porto').
servico(12,   'Ortopedia',           'Hospital de S.Joao',     'Porto').
servico(13,   'Pediatria',           'Hospital de S.Joao',     'Porto').
servico(14, 'Pneumologia',           'Hospital de S.Joao',     'Porto').


% Invariantes
%
% Invariante estrutural: nao permitir a insercao de conhecimento repetido pelo Id
+utente(Id, _, _, _) :: (
                         solucoes(Id, utente(Id, _, _, _), R),
                         comprimento(R, 1)
                         ).
% Invarainte referencial: idade de cada utente pertence [0, 110]
+utente(_, _, Idade, _) :: (
                            integer(Idade),
                            Idade >= 0,
                            Idade =< 110
                           ).

% Invariante estrutural: nao permitir a insercao de conhecimento repetido pelo Id
+servico(Id, _, _, _) :: (
                          solucoes(Id, servico(Id, _, _, _), R),
                          comprimento(R, 1)
                         ).


% Invariante estrutural: nao permitir a insercao de conhecimento repetido pela Descricao por Instituicao
+servico(_, Descricao, Instituicao, _) :: (
                                           solucoes((Descricao, Instituicao), servico(_, Descricao, Instituicao, _), R),
                                           comprimento(R, 1)
                                          ).

% Predicados
%
% Extensao do predicado add_utente: IdUt, Nome, Idade, Cidade -> {V,F}
add_utente(Id, Nome, Idade, Cidade) :- evolucao(utente(Id, Nome, Idade, Cidade)).

% Extensao do predicado remove_utente: IdUt -> {V,F}
remove_utente(Id) :- involucao(utente(Id, _, _, _)).

% Extensao do predicado instituicoes: R -> {V,F}
instituicoes(R) :-
                 solucoes(I, servico(_, _, I, _), L),
                 unicos(L, R).

% Extensao do predicado instituicoes_cidade: Cidade, R -> {V,F}
instituicoes_cidade(Cidade, R) :-
                                solucoes(I, servico(_, _, I, Cidade), L),
                                unicos(L, R).

% Extensao do predicado instituicoes_servico: Servico, R -> {V,F}
instituicoes_servico(Servico, R) :-
                                  solucoes(I, servico(_, Servico, I, _), L),
                                  unicos(L, R).

% Extensao do predicado instituicoes_id: Id, R -> {V,F}
instituicoes_id(Id, R) :- solucoes((I, Id), servico(Id, _, I, _), [(R, _)]).

% Extensao do predicado servicos_instituicao: Instituicao, R -> {V,F}
servicos_instituicao(Instituicao, R) :-
                                     solucoes(S, servico(_, S, Instituicao, _), L),
                                     unicos(L, R).

% Extensao do predicado servicos_cidade: Cidade, R -> {V,F}
servicos_cidade(Cidade, R) :-
                            solucoes(S, servico( _, S, _, Cidade), L),
                            unicos(L, R).

% Extensao do predicado custo_utente: Id, X -> {V,F}
custo_utente(Id, X) :- solucoes( L, consulta(_, Id, _, L), C), list_sum(C, X).

% Extensao do predicado custo_servico: Id, X -> {V,F}
custo_servico(Id, X) :- solucoes( L, consulta(_, _, Id ,L), C), list_sum(C, X).

% Extensao do predicado custo_data: Id, X -> {V,F}
custo_data(Data, X) :- solucoes( L, consulta(Data, _, _, L), C), list_sum(C, X).

% Extensao do predicado custo_instituicao: Id, X -> {V,F}
custo_instituicao(Inst, X) :- solucoes(L, (consulta(_, _, Id, L), servico(Id, _, Inst, _)), C),
                             list_sum(C,X).


% Meta predicados
%
% Extensao do predicado nao: Q -> {V,F}
nao(Q) :- Q, !, fail.
nao(_).

% Extensao do predicado solucoes: F, Q, S -> {V,F}
solucoes(F, Q, _) :- Q, assert(tmp(F)), fail.
solucoes(_, _, S) :- construir(S, []).

% Extensao do predicado construir: S1,S2 -> {V,F}
construir(S1, S2) :- retract(tmp(X)), !, construir(S1, [X | S2]).
construir(S,S).

% Extensao do predicado que permite a evolucao do conhecimento
evolucao(Termo) :-
                 solucoes(Inv, +Termo::Inv, LInv),
                 inserir(Termo),
                 testa(LInv).

inserir(Termo) :- assert(Termo).
inserir(Termo) :- retract(Termo), !, fail.



% Extensao do predicado que permite a involucao do conhecimento
involucao(Termo) :-
                  Termo,
                  solucoes(Inv, -Termo::Inv, LInv),
                  remover(Termo),
                  testa(LInv).

remover(Termo) :- retract(Termo).
remover(Termo) :- assert(Termo), !, fail.

% Extensao do predicado que testa uma lista de invariantes
testa([]).
testa([I|T]) :- I, testa(T).
