% Modulo auxiliar
:- consult('aux.pl').

% Definições iniciais
:- op(900, xfy, '::').
:- dynamic utente/5.
:- dynamic servico/4.
:- dynamic consulta/5.
:- dynamic medico/2.
:- dynamic utente_Id/1.


% Factos
%
% Extensao do predicado utente: IdUt, Nome, Idade, Cidade, IdMed -> {V,F}
utente(0,     'Jose', 55,     'Porto', 1).
utente(1,     'Joao', 21,     'Braga', 1).
utente(2,   'Manuel', 36,     'Porto', 1).
utente(3,   'Carlos', 43, 'Guimaraes', 0).
utente(4,    'Maria', 73, 'Guimaraes', 0).
utente(5,    'Joana',  8,     'Porto', 3).
utente(6, 'Fernando', 49,    'Aveiro', 3).
utente(7,     'Joao', 29,    'Aveiro', 3).
utente(8,      'Ana', 40,     'Braga', 1).
utente(9, 'Catarina', 17,     'Braga', 0).

utente_Id(9).

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


% Extensao do predicado servico: Data, IdUt, IdServ, Custo, IdMed -> {V,F}
consulta(  data(1,1,2019), 0, 2,  50, 1).
consulta(  data(1,2,2019), 0, 1, 100, 0).
consulta(  data(4,2,2019), 1, 1, 100, 3).
consulta(  data(4,2,2019), 3, 2, 123, 2).
consulta(  data(1,3,2019), 2, 0,  30, 3).
consulta(  data(1,4,2019), 3, 6, 150, 2).
consulta( data(9,12,2019), 6, 9,  10, 1).
consulta(data(27,11,2020), 3, 9, 200, 0).
consulta( data(10,5,2020), 6, 14, 50, 0).

%Extensão do predicado medico: ID, Nome -> {V,F}
medico(0, 'Dr. Artur').
medico(1, 'Dr. Eduardo').
medico(2, 'Dr. Filipe').
medico(3, 'Dr. Luís').

% Invariantes
%
% Invariante estrutural: nao permitir a insercao de conhecimento repetido pelo Id
+utente(Id, _, _, _, _) :: (
                         solucoes(Id, utente(Id, _, _, _, _), R),
                         comprimento(R, 1)
                        ).
% Invarainte referencial: idade de cada utente pertence [0, 110]
+utente(_, _, Idade, _, _) :: (
                            integer(Idade),
                            Idade >= 0,
                            Idade =< 110
                           ).

% Invariante estrutural: nao permitir isnserir utente com medico de familia inexistente
+utente(_,_,_,_, IdMed) :: (
                            solucoes(IdMed, medico(IdMed,_), L),
                            comprimento(L,1)
                           ).

%Invariante estrutural: auto incremetar ID's dos utentes
+utente_Id(_) :: (solucoes( I, utente_Id(I), R), 
                  comprimento(R,1)
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

% Invariante estrutural: nao permitir a insercao de conhecimento repetido pelo Id
+medico(Id, _) :: (
                         solucoes(Id, medico(Id, _), R),
                         comprimento(R, 1)
                        ).

% Invariante estrutural: nao permitir remover utentes com consultas associadas
-utente(IdUt,_,_,_,_) :: ( 
                         solucoes(IdUt, consulta(_,IdUt,_,_,_), R),
                         comprimento(R,0)
                         ).

%Invariante Estrutural: nao permitir remover medicos com consultas associadas
-medico(Id, _) :: ( 
                     solucoes(Id, consulta(_,_,_,_,Id), R),
                     comprimento(R,0)
                   ).

%Invariante Estrutural: nao permitir adicionar consultas com Id de utente inexistente
+consulta(_, IdUt, _, _, _) :: (
                                        solucoes( IdUt, 
                                        (utente(IdUt,_,_,_,_)), L),
                                         comprimento(L,N),
                                         N==1).

%Invariante Estrutural: nao permitir adicionar consultas com Id de servico inexistente
+consulta(_, IdServ, _, _, _) :: (
                                        solucoes( IdServ, 
                                        (servico(IdServ,_,_,_)), L),
                                         comprimento(L,N),
                                         N==1).

%Invariante Estrutural: nao permitir adicionar consultas com Id de medico inexistente
+consulta(_, _, _, _, IdMed) :: (
                                        solucoes( IdMed, 
                                        (medico(IdMed,_)), L),
                                         comprimento(L,N),
                                         N==1).

% Predicados
%
% Extensao do predicado add_utente: IdUt, Nome, Idade, Cidade, IdMed -> {V,F}
add_utente(Id, Nome, Idade, Cidade, IdMed) :- evolucao(utente(Id, Nome, Idade, Cidade, IdMed)).

add_utente_a(Nome, Idade, Cidade, IdMed) :- utente_Id(X), involucao(utente_Id(X)),
                                            Y is X + 1,
                                            evolucao(utente(Y, 
                                                            Nome, 
                                                            Idade,
                                                            Cidade,
                                                            IdMed)
                                                    ), 
                                            evolucao(utente_Id(Y
                                          )).

% Extensao do predicado remove_utente: IdUt -> {V,F}
remove_utente(Id) :- involucao(utente(Id, _, _, _,_)).

%Extensão do predicado add_medico: IdMed, Nome -> {V,F}
add_medico(IdMed, Nome) :- evolucao(medico(IdMed, Nome)).

%Extensão do predicado remove_medico: IdMed -> {V,F}
remove_medico(IdMed) :- involucao(medico(IdMed,_)).

%Extensao do predicado add_consulta: Data(D,M,A), IdUt, IdServ, Custo, IdMed -> {V,F}
add_consulta((D,M,A), IdUt, IdServ, Custo, IdMed) :- 
                                                  evolucao( consulta(data(D,M,A),
                                                                     IdUt,
                                                                     IdServ,
                                                                     Custo,
                                                                     IdMed)
                                                          ).

%Extensão do predicado utente_id: IdUt, R -> {V,F}
utente_id(IdUt, R) :- solucoes((IdUt, Nome, Idade, Cidade, (IdMed, Nmed)), 
                                (utente(IdUt,Nome, Idade, Cidade, IdMed),
                                 medico(IdMed, Nmed)), R).

%extensao do predicado utente_nome: Nome, R -> {V,F}
utente_nome(Nome, R) :- solucoes((IdUt,Nome), utente(IdUt,Nome,_,_,_), R).

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
                     solucoes(L, consulta(_, Id, _, L,_), C),
                     lista_soma(C, R).

% Extensao do predicado custo_servico: Id, R -> {V,F}
custo_servico(Id, R) :-
                      solucoes(L, consulta(_, _, Id, L, _), C),
                      lista_soma(C, R).

% Extensao do predicado custo_data: Id, R -> {V,F}
custo_data((D, M, A), R) :-
                          solucoes(L, consulta(data(D, M, A), _, _, L, _), C),
                          lista_soma(C, R).

% Extensao do predicado custo_instituicao: Id, R -> {V,F}
custo_instituicao(Inst, R) :-
                            solucoes(L, (servico(Id,_,Inst,_), 
                                         consulta(_, _, Id, L, _)), C),
                            lista_soma(C, R).

%Extensao do predicado custo_medico: IdMed, R -> {V,F}
custo_medico(IdMed, R) :-
                        solucoes(L, consulta(_,_,_,L,IdMed), C),
                        lista_soma(C,R).

%Extensao do predicado custo_medio: R -> {V,f}
custo_medio(R) :- solucoes(L, consulta(_,_,_,L,_), C),
                  media(C,R).

%Extensao do predicado consulta_medico: IdMed, R -> {V,F}
consulta_medico(IdMed, R) :-
                           solucoes((Data,Esp,Hosp), (consulta(Data,_,IdServ,_,IdMed), 
                                        servico(IdServ,Esp,Hosp,_)), R).

%Extensao do predicado media_idade_utentes: R -> {V,F}
media_idade_utentes(R) :- (
                            solucoes(Idade, utente(_,_,Idade,_,_), L),
                            media(L,R)
                          ).

%Extensao do predicado medico_familia: IdUt, R -> {V,F}
medico_familia(IdUt, R) :- (
                            solucoes((IdMed, Nome), 
                                     (utente(IdUt,_,_,_,IdMed),
                                      medico(IdMed, Nome)), 
                                      R)
                           ).

%extensao do predicado consulta_med_utente: IdUt, R -> {V,F}
consulta_med_utente(IdUt, R) :- 
                              solucoes((Data, IdMed, Nome),
                                       (consulta(Data,IdUt,_,_,IdMed),
                                       medico(IdMed,Nome)),
                                       R
                                ).

%extensao do predicado consulta_med_utente_nf: IdUt, R -> {V,F}
consulta_med_utente_nf(IdUt, R) :-
                              consulta_med_utente(IdUt,A),
                              medico_familia(IdUt, ML),
                              my_fst(ML, L),
                              filtra_medico(L, A, R).

%extensao do predicado melhor_instituicao: R -> {V,F}
melhor_instituicao(R) :- solucoes(IdServ, servico(IdServ,_,_,_), L),
                         mais_rep(L, Y),
                         solucoes(Nome, servico(Y, _, Nome,_), R).

filtra_medico(IdMed, [(_,IdMed,_) | Tail], R) :- filtra_medico(IdMed, Tail, R).
filtra_medico(IdMed, [Head | Tail], R) :- filtra_medico(IdMed, Tail, R),
                                          R = [Head | Tail].

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
