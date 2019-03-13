% Modulo auxiliar
:- consult('aux.pl').

% Definições iniciais
:- dynamic utente/4.


%--------------------------------------------------------
%------------------- Factos -----------------------------
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
servico(15, 'Pediatria', 'Hospital de Braga', 'Braga').



% Extensao do predicado consulta: -> Data, IdUt, IdServ, Custo {V,F}
consulta(data(1,1,2019),0,2,50).
consulta(data(1,2,2019),1,1,100).
consulta(data(1,3,2019),2,0,30).
consulta(data(1,4,2019),3,6,150).
consulta(data(9,12,2019),6,9,10).
consulta(data(27,11,2020),3,9,200).
consulta(data(10,5,2020),6,14,50).


%--------------------------------------------------------
%----------------- Predicados ---------------------------
%--------------------------------------------------------

% Extensao do predicado add_utente: IdUt, Nome, Idade, Cidade -> {V,F}
add_utente(Id, Nome, Idade, Cidade) :-
                                     nao(utente(Id, _, _ ,_)),
                                     Idade >= 0,
                                     Id >= 0,
                                     assert(utente(Id, Nome, Idade, Cidade)).

% Extensao do predicado remove_utente: IdUt -> {V,F}
remove_utente(Id) :- retract(utente(Id, _, _, _)).

% Extensao do predicado instituicoes: R -> {V,F}
instituicoes(R) :-
                 solucoes(I, servico(_, _, I, _), L),
                 unicos(L, R).

% Extensao do predicado instituicoes_cidade: Cidade, R -> {V,F}
instituicoes_cidade(Cidade, R) :-
                                solucoes((I, Cidade), servico(_, _, I, Cidade), L0),
                                unicos(L0, L),
                                lista_pares_fst(L, R).

% Extensao do predicado instituicoes_servico: Servico, R -> {V,F}
instituicoes_servico(Servico, R) :-
                                  solucoes((I, Servico), servico(_, Servico, I, _), L0),
                                  unicos(L0, L),
                                  lista_pares_fst(L, R).

% Extensao do predicado instituicoes_id: Id, R -> {V,F}
instituicoes_id(Id, R) :- solucoes((I, Id), servico(Id, _, I, _), [(R, _)]).

% Extensao do predicado servicos_instituicao: Instituicao, R -> {V,F}
servicos_instituicao(Instituicao, R) :-
                                     solucoes((S, Instituicao), servico(_, S, Instituicao, _), L0),
                                     unicos(L0, L),
                                     lista_pares_fst(L, R).

% Extensao do predicado servicos_cidade: Cidade, R -> {V,F}
servicos_cidade(Cidade, R) :-
                            solucoes((S, Cidade), servico( _, S, _, Cidade), L0),
                            unicos(L0, L),
                            lista_pares_fst(L, R).



% Extensao do predicado identificar os utentes de um serviço
utentes_servico(Servico,R) :-
    solucoes((ID,Servico), servico(ID,Servico,_,_),R0),
    unicos(R0,R1),
    lista_pares_fst(R1,R2),
    ut_instit_aux(R2,R).
    
    %solucoes((U,_), consulta(_,U,R2,_), R3),
    %unicos(R3,R4),
    %lista_pares_fst(R4,R).


% Extensao do predicado identificar os utentes de um instituicao
ut_instit_aux([], L).
ut_instit_aux((IdServ|T), L) :-
    solucoes((U,IdServ), consulta(_,U,IdServ,_), R0),
    unicos(R0,R1),
    lista_pares_fst(R1,R2),
    append(R2,R3,L0),
    unicos(L0,L),
    ut_instit_aux(T,R3).


utentes_instituicao(Instit,R) :-
    solucoes((ID,Instit), servico(ID,_,Instit,_), R0),
    unicos(R0,R1),
    lista_pares_fst(R1,R2),
    ut_instit_aux(R2,R).



% Extensao do predicado identificar utentes por diferentes critérios de selecao
% 1 - ID
search_utente_id(Id,R) :-
    solucoes((U,Id), utente(Id,U,_,_), R0),
    unicos(R0,R1),
    lista_pares_fst(R1,R2).

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