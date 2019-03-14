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


% Extensao do predicado servico: Data, IdUt, IdServ, Custo -> {V,F}
consulta(  data(1,1,2019), 0, 2,  50).
consulta(  data(1,2,2019), 1, 1, 100).
consulta(  data(4,2,2019), 1, 1, 100).
consulta(  data(4,2,2019), 3, 2, 123).
consulta(  data(1,3,2019), 2, 0,  30).
consulta(  data(1,4,2019), 3, 6, 150).
consulta( data(9,12,2019), 6, 9,  10).
consulta(data(27,11,2020), 3, 9, 200).
consulta( data(10,5,2020), 6, 14, 50).

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

% Extensao do predicado custo_utente: Id, R -> {V,F}
custo_utente(Id, R) :-
                     solucoes(L, consulta(_, Id, _, L), C),
                     lista_soma(C, R).

% Extensao do predicado custo_servico: Id, R -> {V,F}
custo_servico(Id, R) :-
                      solucoes(L, consulta(_, _, Id, L), C),
                      lista_soma(C, R).

% Extensao do predicado custo_data: Id, R -> {V,F}
custo_data((D, M, A), R) :-
                          solucoes(L, consulta(data(D, M, A), _, _, L), C),
                          lista_soma(C, R).

% Extensao do predicado custo_instituicao: Id, R -> {V,F}
custo_instituicao(Inst, R) :-
                            solucoes(L, consulta(_, _, Inst, L), C),
                            lista_soma(C, R).


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


% Extensao do predicado identificar os utentes de um serviço



% Extensao do predicado identificar os utentes de um instituicao



% Extensao do predicado identificar utentes por diferentes critérios de selecao
% 1 - ID
search_utente_id(Id,R) :-
    solucoes((U,Id), utente(Id,U,_,_), R0),
    unicos(R0,R1),
    lista_pares_fst(R1,R).

% 2 - Nome
search_utente_nome(Nome,R) :-
    solucoes((Nome,Idade), utente(_,Nome,Idade,_), R0),
    unicos(R0,R).

% 3 - Nome e Cidade
search_utente_nome_e_cidade(Nome, Cidade, R) :-
    solucoes((Nome,Cidade), utente(_,Nome,_,Cidade), R0),
    unicos(R0,R).


% Extensao do predicado identificar servicos por diferentes critério de selecao
% 1 - ID
search_servico_id(ID,R) :-
    solucoes((Desc,ID), servico(ID,Desc,_,_), R0),
    unicos(R0,R).

% 2 - Descricao e/ou cidade
search_servico_descricao(Desc,Cid,R) :-
    solucoes((Inst,Cid), servico(_,Desc,Inst,Cid), R0),
    unicos(R0,R).

% Extensao do predicado identificar consultas por diferentes criterios de selecao
% 1 - Data
search_consulta_data(Data,R) :-
    solucoes((Data,U), consulta(Data,U,_,_), R0),
    unicos(R0,R).

% 2 - Utentes envolvidos


% 3 - Servico envolvidos


% 4 - Custo superior a um valor
filtra_custo([], _, L).
filtra_custo((U,D,C)|T, N, L) :-
    C > N,
    filtra_custo(T,N,L0).

search_consulta_valor_superior(N,R) :-
    solucoes((U,Data, Custo), consulta(Data,U,_,Custo), R0),
    unicos(R0,R1),
    filtra_custo(R1,N,R2).