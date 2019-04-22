% Modulo auxiliar
:- consult('aux.pl').
% Definições iniciais
:- op(900, xfy, '::').
:- op(900, xfy, ':~:').
:- dynamic utente/4.
:- dynamic cuidado/6.
:- dynamic prestador/4.
:- dynamic utente_Id/1.
:- dynamic nulo/1.
:- dynamic impreciso/1.
:- dynamic excecao/1.
:- dynamic '::'/2.
:- op(995, fx, '@|').  % operador de negacao
:- op(996, xfy, '@&').  % operador de conjuncao
:- op(997, xfy, '@$').  % operador de disjuncao
:- op(997, xfy, '@#').  % operador de negacao exclusiva
:- op(998, xfx, '@=>' ).  % operador de implicacao
:- op(999, xfx, '@<=>'). % operador de equivalencia


si(P0 @<=> P1, V) :-
                  si(P0, V0),
                  si(P1, V1),
                  equivalencia(V0, V1, V), !.
si(P0 @=> P1, V) :-
                 si(P0, V0),
                 si(P1, V1),
                 implicacao(V0, V1, V), !.
si(P0 @$ P1, V) :-
                 si(P0, V0),
                 si(P1, V1),
                 disjuncao(V0, V1, V), !.
si(P0 @& P1, V) :-
                 si(P0, V0),
                 si(P1, V1),
                 conjuncao(V0, V1, V), !.

si(P0 @# P1, V) :-
                  si(P0, V0),
                  si(P1, V1),
                  negacaoExclusiva(V0, V1, V), !.

si(@| P0, V) :- si(P0, P1), negacao(P1, V), !.
si(P, verdadeiro) :- P.
si(P, falso) :- -P.
si(P, desconhecido) :-
                     nao(P),
                     nao(-P).

equivalencia(Y, Y, verdadeiro) :- Y \= desconhecido.
equivalencia(desconhecido, _, desconhecido).
equivalencia(_, desconhecido, desconhecido).
equivalencia(verdadeiro, falso, falso).
equivalencia(falso, verdadeiro, falso).

implicacao(verdadeiro, Y, Y).
implicacao(falso, _, verdadeiro).
implicacao(desconhecido, Y, Y) :- Y \= falso.
implicacao(desconhecido, falso, desconhecido).

disjuncao(verdadeiro, _, verdadeiro).
disjuncao(falso, Y, Y).
disjuncao(desconhecido, Y, desconhecido) :- Y \= verdadeiro.
disjuncao(desconhecido, verdadeiro, verdadeiro).

conjuncao(verdadeiro, Y, Y).
conjuncao(falso, _, falso).
conjuncao(desconhecido, falso, falso).
conjuncao(desconhecido, Y, desconhecido) :- Y \= falso.

negacao(verdadeiro, falso).
negacao(falso, verdadeiro).
negacao(desconhecido, desconhecido).

negacaoExclusiva(P, Q, R) :-
                           conjuncao(P, Q, R0), negacao(R0, R1),
                           disjuncao(P, Q, R2),
                           conjuncao(R1, R2, R).
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
+utente(Id, _, _, _) :: (
                         solucoes(Id, utente(Id, _, _, _), R),
                         comprimento(R, 1)
                     ).

%Invariante que define existir uma so negação explicita
+(-utente(Id , Nome, Idade, Cidade)) :: (solucoes(Id, -utente(Id , Nome, Idade, Cidade),S),
                                         comprimento(S,1)
                                     ).


%Invariante que define que tem de existir uma e uma so negaçao explicita.
 +(-cuidado(Id, Data, IdU, IdP, Desc, Cust)) :: (solucoes(Id, -cuidado(Id, Data, IdU, IdP, Desc, Cust), S),
	                                          comprimento(S, 1)
                                           ).

%Invariante que define existir uma so negação explicita
+(-prestador(Id, Nome, Espc, Inst)) :: (solucoes(Id, -prestador(Id, Nome, Espc, Inst), S),
                                        comprimento(S,1)
                                       ).


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


%Invariante que nao permite adicionar conhecimento imperfeito na presença de perfeito
+utente(Id,_,_,_) :~: (nao(perfeito(utente(Id)))).

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
 %
 % Evolucao de conhecimento perfeito que remove conhecimento impreciso/incerto

evolucao_perfeito(utente(Id, N, I, M)) :-
	solucoes(Inv, +utente(Id, N, I, M)::Inv, LInv),
  %remover_impreciso(utente(IdUt,Nome,Idade,Morada)),
	inserir(utente(Id, N, I, M)),
  testa(LInv),
  inserir(perfeito(utente(Id))).

evolucao_perfeito((-utente(IdUt, Nome, Idade, Morada))) :-
	solucoes(Inv, +(-utente(IdUt,Nome,Idade,Morada))::Inv, LInv),
	testa(LInv),
  %	removerImpreciso(utente(IdUt,Nome,Idade,Morada)),
	inserir((-utente(IdUt,Nome,Idade,Morada))),
  inserir(perfeito(utente(IdUt))).

involucao_perfeito(utente(IdUt, Nome, Idade, Morada)) :-
	utente(IdUt, Nome, Idade, Morada),
	solucoes(Inv, -utente(IdUt,Nome,Idade,Morada)::Inv, LInv),
	testa(LInv),
	remover(utente(IdUt, Nome, Idade, Morada)),
  remover(perfeito(utente(IdUt))).

involucao_perfeito((-utente(IdUt, Nome, Idade, Morada))) :-
	utente(IdUt, Nome, Idade, Morada),
	solucoes(Inv, -(-utente(IdUt,Nome,Idade,Morada))::Inv, LInv),
	testa(LInv),
	remover(utente(IdUt, Nome, Idade, Morada)),
  remover(perfeito(utente(IdUt))).

%Inserir Exceções
insere_excecoes([]).
insere_excecoes([utente(IdUt, Nome, Idade, Morada)|Es]) :-
	inserir(excecao(utente(IdUt, Nome, Idade, Morada))),
	inserir(impreciso(utente(IdUt))),
	insere_excecoes(Es).

%Remover exceções
remove_excecoes([]).
remove_excecoes([utente(IdUt,Nome,Idade,Morada)|Ps]) :-
	remover(excecao(utente(IdUt, Nome, Idade, Morada))),
	remover(impreciso(utente(IdUt))),
	remove_excecoes(Ps).


%Evolução do conhecimento incerto da idade de um utente
evolucao_incerto_idade(utente(IdUt, Nome, Idade, Morada)) :-
	solucoes(Inv, +utente(IdUt, Nome, Idade, Morada)::Inv, LInv2),
	inserir((excecao(utente(Id,N,_,M)) :-
	       utente(Id,N,Idade,M))),
	inserir(utente(IdUt, Nome, Idade, Morada)),
	testa(LInv2).

%Evolução do conhecimento incerto do custo de um cuidado
evolucao_incerto_custo(cuidado(Id, Data, IdUt, IdPrest, Desc, Custo)) :-
	solucoes(Inv, +cuidado(Id, Data, IdUt, IdPrest, Desc, Custo)::Inv, LInv2),
	inserir((excecao(cuidado(I, D, IU, IP, D, _)) :-
	       cuidado(I, D, IU, IP, D, Custo))),
	inserir(cuidado(Id, Data, IdUt, IdPrest, Desc, Custo)),
	testa(LInv2).

%Involução incerto idade utente
involucao_incerto_idade(utente(IdUt, Nome, Idade, Morada)) :-
	utente(IdUt, Nome,Idade,Morada),
	incerto_idade(utente(IdUt, _)),
	solucoes(Inv, -utente(IdUt, Nome, Idade, Morada)::Inv, LInv),
	remover((excecao(utente(Id,N,_,M)) :-
		utente(Id,N,Idade,M))),
	remover(utente(IdUt, _, _ ,_)),
	testa(LInv).

%Involução incerto custo de um cuidado
involucao_incerto_custo(cuidado(Id, Data, IdUt, IdPrest, Desc, Custo)) :-
	cuidado(Id, Data, IdUt, IdPrest, Desc, Custo),
	incerto_custo(Id, _),
	solucoes(Inv, -cuidado(Id, Data, IdUt, IdPrest, Desc, Custo)::Inv, LInv),
	remover((excecao(cuidado(I, D, IU, IP, D, _)) :-
	       cuidado(I, D, IU, IP, D, Custo))),
	remover(cuidado(Id, Data, IdUt, IdPrest, Desc, Custo)),
	testa(LInv).

%Evolução de conhecimento impreciso
evolucao_impreciso([utente(IdUt, Nome, Idade, Morada)|T]) :-
	T \= [],
	utente_igual(T, IdUt),
  %remove_incerto(utente(IdUt, Nome, Idade, Morada)),
  inserir(impreciso(IdUt)),
	insere_excecoes([utente(IdUt, Nome, Idade, Morada)|T]),
	testaInvs([utente(IdUt, Nome, Idade, Morada)|T]).

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
	remover((excecao(utente(Id,N,_,M)) :-
		utente(Id,N,I,M))),
	remover(utente(IdUt, _, _ ,_)),
  remover(incerto_idade(utente(IdUt, _))).

%Involução do conhecimento impreciso
involucao_impreciso([utente(Id,Nome,Idade,Morada) | T]) :-
    procura_excecao([utente(Id,Nome,Idade,Morada) | T]),
    utente_igual(T, Id),
    remove_excecoes([utente(Id,Nome,Idade,Morada) | T]),
    testaInvolInvs([utente(Id,Nome,Idade,Morada) | T]).

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
  solucoes(Inv, +utente(IdUt, Nome, Idade, Morada):~:Inv, LInv1),
	assert(nulo(Idade)),
	inserir((excecao(utente(Id,N,I,M)) :-
	       utente(Id,N,Idade,M))),
	inserir((+utente(Id,N,I,M) :: (
				       solucoes(Id,(utente(Id,_,Idade,_), nulo(Idade)),S),
				       comprimento(S,0)
				     ))),
	inserir(utente(IdUt, Nome,Idade,Morada)),
	testa(LInv),
  testa(LInv1).

% Involucao do conhecimento interdito relativo a idade de um utente
involucao_interdito_idade(utente(IdUt, Nome, Idade, Morada)) :-
	utente(IdUt, Nome, Idade, Morada),
	nulo(Idade),
	solucoes(Inv, -utente(IdUt, Nome, Idade, Morada)::Inv, LInv),
	remover(nulo(Idade)),
	remover((excecao(utente(Id,N,I,M)) :-
	       utente(Id,N,Idade,M))),
	remover((+utente(Id,N,I,M) :: (
				       solucoes(Id,(utente(Id,_,Idade,_), nulo(Idade)),S),
				       comprimento(S,0)
				     ))),
	remover(utente(IdUt, Nome,Idade,Morada)),
	testa(LInv).

%Predicado para saber a idade de um utente.
idade_utente(Id, I) :- utente(Id, _, I, _).
-idade_utente(Id, I) :- nao(utente(Id, _, I, _)), nao(excecao(utente(Id, _, I, _))).


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
