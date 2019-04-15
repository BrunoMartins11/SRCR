% Modulo auxiliar
:- consult('aux.pl').

% Definições iniciais
:- op(900, xfy, '::').
:- dynamic utente/4.
:- dynamic cuidado/6.
:- dynamic prestador/4.
:- dynamic utente_Id/1.


% Factos
%
% Extensao do predicado utente: IdUt, Nome, Idade, Cidade -> {V,F,D}
utente(0,     'Jose', 55,     'Porto' ).
utente(1,     'Joao', 21,     'Braga' ).
utente(2,   'Manuel', 36,     'Porto' ).
utente(3,   'Carlos', 43, 'Guimaraes' ).
utente(4,    'Maria', 73, 'Guimaraes' ).
utente(5,    'Joana',  8,     'Porto' ).
utente(6, 'Fernando', 49,    'Aveiro' ).
utente(7,     'Joao', 29,    'Aveiro' ).
utente(8,      'Ana', 40,     'Braga' ).
utente(9, 'Catarina', 17,     'Braga' ).

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
excecao(utente(14, 'Alfredo', 74, 'Rua de Baixo')).
excecao(utente(14, 'Alfredo', 74, 'Rua de Barros')).
 
%Conhecimento Interdito
cuidado(4, data(23,2,2018), nulo2, 'Consulta Rotina', 123).
excecao(cuidado(Id, Data, IdUt, IdServ, Desc, Custo)) :-
                                                       cuidado(Id, Data, nulo2, IdServ, Custo, IdPro).
nulo(nulo2).
+cuidado(Id, Data, IdUt, IdServ, Desc, Custo) :: (
    solucoes(IdUtVar, (cuidado(4, data(23,2,2018), nulo2, 'Consulta Rotina', 123)), nao(nulo(IdUtVar)), S),
    comprimento(S,0)
).
  
  
  
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
