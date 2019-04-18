% Modulo auxiliar
:- consult('aux.pl').
% Definições iniciais
:- op(900, xfy, '::').
:- dynamic utente/4.
:- dynamic cuidado/6.
:- dynamic prestador/4.
:- dynamic utente_Id/1.
:- dynamic nulo/1.
:- dynamic impreciso/1.



% Factos
%
% Extensao do predicado utente: IdUt, Nome, Idade, Cidade -> {V,F,D}
utente(0,     'Jose', 55,     'Porto' ).
perfeito(utente(0)).
utente(1,     'Joao', 21,     'Braga' ).
perfeito(utente(1)).
utente(2,   'Manuel', 36,     'Porto' ).
perfeito(utente(2)).
utente(3,   'Carlos', 43, 'Guimaraes' ).
perfeito(utente(3)).
utente(4,    'Maria', 73, 'Guimaraes' ).
perfeito(utente(4)).
utente(5,    'Joana',  8,     'Porto' ).
perfeito(utente(5)).
utente(6, 'Fernando', 49,    'Aveiro' ).
perfeito(utente(6)).
utente(7,     'Joao', 29,    'Aveiro' ).
perfeito(utente(7)).
utente(8,      'Ana', 40,     'Braga' ).
perfeito(utente(8)).
utente(9, 'Catarina', 17,     'Braga' ).
perfeito(utente(9)).


utente_Id(9).

%extensao do predicado prestador: IdPrest, Nome, Especialidade, Instituição -> {V, F ,D}

prestador(0, 'Joao', 'Ortopedia', 'Hospital Privado de Braga').

%Extensao do predicado cuidado: Id, Data, IdUt, IdPrest, Descriçao, Custo -> {V, F, D}

cuidado(0, data(12,12,12), 4, 0, 'Protese', 100).

% Invariantes
% Invariante estrutural: nao permitir a insercao de conhecimento repetido pelo Id
+utente(Id, _, _, _, _) :: (
                         solucoes(Id, utente(Id, _, _, __), R),
                         comprimento(R, 1)
                        ).
% Invarainte referencial: idade de cada utente pertence [0, 110]
+utente(_, _, Idade, _) :: (
                            integer(Idade),
                            Idade >= 0,
                            Idade =< 110
                           ).

%Invariante que define existir uma so negação explicita
+(-utente(Id , Nome, Idade, Cidade)) :: (solucoes(Id, -utente(Id , Nome, Idade, Cidade),S),
                                         comprimento(S,N),
                                         N==1).


%Invariante que define que tem de existir uma e uma so negaçao explicita.
 +(-cuidado(Id, Data, IdU, IdP, Desc, Cust)) :: 
                                           (solucoes(Id, -cuidado(Id, Data, IdU, IdP, Desc, Cust), S),
	                                          comprimento(S, N),
	                                          N == 1
                                           ).

%Invariante que define existir uma so negação explicita
+(-prestador(Id, Nome, Espc, Inst)) :: (solucoes(Id, -prestador(Id, Nome, Espc, Inst), S),
                                        comprimento(S,N),
                                        N==1).


%Invariante estrutural: auto incremetar ID's dos utentes
+utente_Id(_) :: (solucoes( I, utente_Id(I), R),
                  comprimento(R,1)
                ).
% Invariante estrutural: nao permitir remover utentes com consultas associadas
-utente(Id,_,_,_) :: (nao( cuidado(_,Id,_,_,_) )).

%Extensao do predicado que define a negação forte de um utente.
-utente(IdUt, Nome, Idade, Morada) :-
                                  nao(utente(IdUt, Nome, Idade, Morada)),
	                                nao(excecao(utente(IdUt, Nome, Idade, Morada))).
%Extensao d predicado que define a negaçao forte de um cuidado.
-cuidado(Id,Data, IdU, IdP, Desc, Cust) :-
                                      nao(cuidado(Id,Data, IdU, IdP, Desc, Cust)),
	                                    nao(excecao(cuidado(Id,Data, IdU, IdP, Desc, Cust))).

%Extensao do predicado que define a negação forte de prestador.
-prestador(Id, Nome, Espc, Inst) :- nao(prestador(Id, Nome, Espc, Inst)),
                                    nao(excecao(prestador(Id, Nome, Espc, Inst))).



%Conhecimento incerto.
nulo(nulo1).
cuidado(1,data(4,4,2018), 4, 6,'Operacao' , nulo1).
excecao(cuidado(Id,Data, IdU, IdP, Desc, Cust)) :-
                                                 cuidado(Data, IdUt, IdServ, Desc, nulo1).
                                               
%Conhecimento impreciso
excecao(utente(24, 'Antonio', 32, 'Porto')).
excecao(utente(24, 'Antonio', 32, 'Matosinhos')).
impreciso(utente(24)). 

%Conhecimento Interdito
cuidado(4, data(23,2,2018), nulo2, 'Consulta Rotina', 123).
excecao(cuidado(Id, Data, IdUt, IdServ, Desc, Custo)) :-
                                                       cuidado(Id, Data, nulo2, IdServ, Custo, IdPro).
nulo(nulo2).
+cuidado(Id, Data, IdUt, IdServ, Desc, Custo) :: (
    solucoes(IdUtVar, (cuidado(4, data(23,2,2018), nulo2, 'Consulta Rotina', 123)), nao(nulo(IdUtVar)), S),
    comprimento(S,0)
).
  
 % Evolucao de conhecimento perfeito que remove conhecimento impreciso/incerto

evolucao_perfeito(utente(IdUt,Nome,Idade,Morada)) :-
	solucoes(Inv, +utente(IdUt,Nome,Idade,Morada)::Inv, LInv),
	testa(LInv),
	removerImpreciso(utente(IdUt,Nome,Idade,Morada)),
	assert(utente(IdUt,Nome,Idade,Morada)),
  assert(perfeito(utente(IdUtU))).

evolucao_perfeito((-utente(IdUt, Nome, Idade, Morada))) :-
	solucoes(Inv, +(-utente(IdUt,Nome,Idade,Morada))::Inv, LInv),
	testa(LInv),
	removerImpreciso(utente(IdUt,Nome,Idade,Morada)),
	assert((-utente(IdUt,Nome,Idade,Morada))),
  assert(perfeito(utente(IdUt))).

involucao_perfeito(utente(IdUt, Nome, Idade, Morada)) :-
	utente(IdUt, Nome, Idade, Morada),
	solucoes(Inv, -utente(IdUt,Nome,Idade,Morada)::Inv, LInv),
	testa(LInv),
	retract(utente(IdUt, Nome, Idade, Morada)),
  retract(perfeito(utente(IdUt))).

involucao_perfeito((-utente(IdUt, Nome, Idade, Morada))) :-
	utente(IdUt, Nome, Idade, Morada),
	solucoes(Inv, -(-utente(IdUt,Nome,Idade,Morada))::Inv, LInv),
	testa(LInv),
	retract(utente(IdUt, Nome, Idade, Morada)),
  retract(perfeito(utente(IdUt))).

%Inserir Exceções
insere_excecoes([]).
insereExcecoes([utente(IdUt, Nome, Idade, Morada)|Es]) :-
	assert(excecao(utente(IdUt, Nome, Idade, Morada))),	
	assert(impreciso(utente(IdUt))),
	insere_excecoes(Es).

%Remover exceções
remove_excecoes([]).
remove_excecoes([utente(IdUt,Nome,Idade,Morada)|Ps]) :-
	retract(excecao(utente(IdUt, Nome, Idade, Morada))),
	retract(impreciso(utente(IdUt))),
	remove_excecoes(Ps).

% Meta predicados
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
