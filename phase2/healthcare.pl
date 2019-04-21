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
-utente(9, 'Catarina', 23, 'Braga' ).


utente_Id(9).

%extensao do predicado prestador: IdPrest, Nome, Especialidade, Instituição -> {V, F ,D}

prestador(0, 'Joao', 'Ortopedia', 'Hospital Privado de Braga').
prestador(1, 'André', 'Cardio', 'Hospital de Guimaraes').
%Extensao do predicado cuidado: Id, Data, IdUt, IdPrest, Descriçao, Custo -> {V, F, D}

cuidado(0, data(12,12,12), 4, 0, 'Protese', 100).
cuidado(1, data(11,11,11), 7, 1, 'Pacemaker', 200).

% Invariantes
% Invariante estrutural: nao permitir a insercao de conhecimento repetido pelo Id
+utente(Id, _, _, _, _) :: (
                         solucoes(Id, utente(Id, _, _, __), R),
                         comprimento(R, 1)
                        ).
% Invarainte referencial: idade de cada utente pertence [0, 110]
%+utente(_, _, Idade, _) :: (
%                           integer(Idade),
%                           Idade >= 0,
%                           Idade =< 110
%                          ).

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
  %remover_impreciso(utente(IdUt,Nome,Idade,Morada)),
	assert(utente(IdUt,Nome,Idade,Morada)),
  assert(perfeito(utente(IdUt))).

evolucao_perfeito((-utente(IdUt, Nome, Idade, Morada))) :-
	solucoes(Inv, +(-utente(IdUt,Nome,Idade,Morada))::Inv, LInv),
	testa(LInv),
  %	removerImpreciso(utente(IdUt,Nome,Idade,Morada)),
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
insere_excecoes([utente(IdUt, Nome, Idade, Morada)|Es]) :-
	assert(excecao(utente(IdUt, Nome, Idade, Morada))),	
	assert(impreciso(utente(IdUt))),
	insere_excecoes(Es).

%Remover exceções
remove_excecoes([]).
remove_excecoes([utente(IdUt,Nome,Idade,Morada)|Ps]) :-
	retract(excecao(utente(IdUt, Nome, Idade, Morada))),
	retract(impreciso(utente(IdUt))),
	remove_excecoes(Ps).


%Evolução do conhecimento incerto da idade de um utente
evolucao_incerto_idade(utente(IdUt, Nome, Idade, Morada)) :- 
	solucoes(Inv, +utente(IdUt, Nome, Idade, Morada)::Inv, LInv2),
	testa(LInv2),
	assert((excecao(utente(Id,N,_,M)) :-
	       utente(Id,N,Idade,M))),
	assert(utente(IdUt, Nome, Idade, Morada)),
	assert(incerto_idade(utente(IdUt,Idade))).

%Evolução do conhecimento incerto do custo de um cuidado
evolucao_incerto_custo(cuidado(Id, Data, IdUt, IdPrest, Desc, Custo)) :- 
	solucoes(Inv, +cuidado(Id, Data, IdUt, IdPrest, Desc, Custo)::Inv, LInv2),
	testa(LInv2),
	assert((excecao(cuidado(I, D, IU, IP, D, _)) :-
	       cuidado(I, D, IU, IP, D, Custo))),
	assert(cuidado(Id, Data, IdUt, IdPrest, Desc, Custo)),
	assert(incerto_custo(Id, Custo)).

%Involução incerto idade utente
involucao_incerto_idade(utente(IdUt, Nome, Idade, Morada)) :-
	utente(IdUt, Nome,Idade,Morada),
	incerto_idade(utente(IdUt, _)),
	solucoes(Inv, -utente(IdUt, Nome, Idade, Morada)::Inv, LInv),
	testa(LInv),
	retract((excecao(utente(Id,N,_,M)) :-
		utente(Id,N,Idade,M))),
	retract(utente(IdUt, _, _ ,_)),
	retract(incerto_idade(utente(IdUt, _))).

%Involução incerto custo de um cuidado
involucao_incerto_custo(cuidado(Id, Data, IdUt, IdPrest, Desc, Custo)) :-
	cuidado(Id, Data, IdUt, IdPrest, Desc, Custo),
	incerto_custo(Id, _),
	solucoes(Inv, -cuidado(Id, Data, IdUt, IdPrest, Desc, Custo)::Inv, LInv),
	testa(LInv),
	retract((excecao(cuidado(I, D, IU, IP, D, _)) :-
	       cuidado(I, D, IU, IP, D, Custo))),
	retract(cuidado(Id, Data, IdUt, IdPrest, Desc, Custo)),
	retract(incerto_custo(Id, _)).

%Evolução de conhecimento impreciso
evolucao_impreciso([utente(IdUt, Nome, Idade, Morada)|T]) :-
	T \= [],
	utente_igual(T, IdUt),
	testaInvs([utente(IdUt, Nome, Idade, Morada)|T]),
  %remove_incerto(utente(IdUt, Nome, Idade, Morada)),
  assert(impreciso(IdUt)),
	insere_excecoes([utente(IdUt, Nome, Idade, Morada)|T]).

testaInvs([]).
testaInvs([P|Ps]) :-
	solucoes(Inv, +P::Inv, LInv1),
	testa(LInv1),	 
	testaInvs(Ps).

utente_igual([], _).
utente_igual([utente(Id1, _, _, _) | T], Id2) :-
	Id1 == Id2,
	utente_igual(T, Id2).

remove_incerto(utente(IdUt,_,_,_)) :-
	incerto_idade(utente(IdUt,I)),
	retract((excecao(utente(Id,N,_,M)) :-
		utente(Id,N,I,M))),
	retract(utente(IdUt, _, _ ,_)),
  retract(incerto_idade(utente(IdUt, _))).

%Involução do conhecimento impreciso
involucao_impreciso([utente(Id,Nome,Idade,Morada) | T]) :-
    procura_excecao([utente(Id,Nome,Idade,Morada) | T]),
    utente_igual(T, Id),
    testaInvolInvs([utente(Id,Nome,Idade,Morada) | T]),
    remove_excecoes([utente(Id,Nome,Idade,Morada) | T]).

testaInvolInvs([]).
testaInvolInvs([P|Ps]) :- 
    solucoes(Inv, -P::Inv, LInv),
    testa(LInv),
    testaInvolInvs(Ps).

procura_excecao([]).
procura_excecao([T|Ts]) :-
    excecao(T), procura_excecao(Ts).

%Evolucao do conhecimento interdito sobre a idade de um utente
evolucao_interdito_idade(utente(IdUt, Nome, Idade, Morada)) :-
	solucoes(Inv, +utente(IdUt, Nome, Idade, Morada)::Inv, LInv),
	testa(LInv),
	assert(nulo(Idade)),
	assert((excecao(utente(Id,N,I,M)) :-
	       utente(Id,N,Idade,M))),
	assert((+utente(Id,N,I,M) :: (
				       solucoes(Id,(utente(Id,_,Idade,_), nulo(Idade)),S),
				       comprimento(S,0)
				     ))),
	assert(utente(IdUt, Nome,Idade,Morada)).

% Involucao do conhecimento interdito relativo a idade de um utente
involucao_interdito_idade(utente(IdUt, Nome, Idade, Morada)) :-
	utente(IdUt, Nome, Idade, Morada),
	nulo(Idade),
	solucoes(Inv, -utente(IdUt, Nome, Idade, Morada)::Inv, LInv),
	testa(LInv),
	retract(nulo(Idade)),
	retract((excecao(utente(Id,N,I,M)) :-
	       utente(Id,N,Idade,M))),
	retract((+utente(Id,N,I,M) :: (
				       solucoes(Id,(utente(Id,_,Idade,_), nulo(Idade)),S),
				       comprimento(S,0)
				     ))),
	retract(utente(IdUt, Nome,Idade,Morada)).

%Predicado para saber a idade de um utente.
idade_utente(Id, I) :- utente(Id, _, I, _).

%Predicado para saber o custo de um cuidado.
custo_cuidado(Id, C) :- cuidado(Id, _,_,_,_, C).

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
