/*  Part of Extended Tools for SWI-Prolog

    Author:        Edison Mera
    E-mail:        efmera@gmail.com
    WWW:           https://github.com/edisonm/stchecks
    Copyright (C): 2022, Process Design Center, Breda, The Netherlands.
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

:- module(module_links,
          [ current_chain_link/4,
            depends_of_db/6,
            loop_to_chain/2,
            module_pred_chains/6,
            module_pred_links/2,
            module_uses/3,
            preds_uses/3,
            update_depends_of/0,
            cleanup_depends_of/0
          ]).

:- use_module(library(lists)).
:- use_module(library(calls_to)).
:- use_module(library(solution_sequences)).

:- multifile
        update_depends_of_hook/0.

ref_head('<assertion>'(M:H), M, H).
ref_head(M:H, M, H).
ref_head(clause(Ref), M, H) :-
    freeze(Ref, clause(M:H, _, Ref)).

pred_calls_to(AH, AM, H, CM) :-
    ref_head(Ref, AM, AH),
    calls_to(Ref, CM, H).

:- dynamic
    depends_of_db/6.

update_depends_of :-
    update_depends_of_1,
    forall(update_depends_of_hook, true),
    update_depends_of_n.

cleanup_depends_of :-
    retractall(depends_of_db(_, _, _, _, _, _)).

update_depends_of_1 :-
    forall(( pred_calls_to(AH, AM, TH, CM),
             predicate_property(CM:TH, implementation_module(TM)),
             \+ depends_of_db(AH, AM, TH, TM, CM, _)
           ),
           ( functor(AH, AF, AA), functor(AP, AF, AA),
             functor(TH, TF, TA), functor(TP, TF, TA),
             assertz(depends_of_db(AP, AM, TP, TM, CM, 1))
           )).

% resolve recursion explicitly for those dependencies inside the same module to
% avoid performance issues: we use tabling, but we also use an index to prevent
% performance problems, otherwise it will try all the possible paths between two
% predicates, which is not needed actually

update_depends_of_n :-
    update_depends_of_n(1).

update_depends_of_n(N1) :-
    succ(N1, N),
    forall(( depends_of_db(AH, AM, IH, IM, CM, N1),
             depends_of_db(IH, IM, TH, TM, CM, 1),
             \+ depends_of_db(AH, AM, TH, TM, CM, _)
           ),
           assertz(depends_of_db(AH, AM, TH, TM, CM, N))),
    ( depends_of_db(_, _, _, _, _, N)
    ->update_depends_of_n(N)
    ; true
    ).

module_pred_links(ModuleL1, PILL) :-
    % Create a circular linked list:
    append(ModuleL1, ModuleL, ModuleL),
    findall(PI, module_pred_1st(forw, ModuleL, PI), PIU),
    sort(PIU, PI1),
    module_pred_link_loop(ModuleL, PI1, [], PILL).

module_pred_link_loop([Module1, Module2|ModuleL], PI1, PILL1, PILL) :-
    % Fixpoint algorithm, it will stop when PI2 is an empty list or
    % when PI2 was already obtained in a previous iteraction:
    module_pred(forw, Module1, Module2, PI1, PI2),
    ( PI2 = []
    ->PILL = [Module2:PI2, Module1:PI1|PILL1]
    ; member(Module2:PI2, PILL1)
    ->PILL = [Module1:PI1|PILL1]
    ; module_pred_link_loop([Module2|ModuleL], PI2, [Module1:PI1|PILL1], PILL)
    ).

module_pred_chains(forw, M1, M2, C, PILL, PIL) :-
    module_pred_chains_2(forw, M2, M1, C, PILR, PIL),
    reverse(PILR, PILL).
module_pred_chains(back, M2, M3, C, PILL, PIL) :-
    reverse(C, R),
    module_pred_chains_2(back, M2, M3, R, PILR, PIL),
    reverse(PILR, PILL).

module_pred_chains_2(D, M2, M1, P1, [M1:PI1|PILL], PIL) :-
    append(P1, [M2], P2),
    findall(PI, module_pred_1st(D, [M1|P2], PI), PIU),
    sort(PIU, PI1),
    foldl(module_pred(D), [M1|P1], P2, PILL, PI1, PIL).

module_pred_1st(back, [Module3, Module2|_], F3/A3) :-
    depends_of_db(_, _, H3, Module3, Module2, 1),
    functor(H3, F3, A3).
module_pred_1st(forw, [Module1, Module2|_], PI) :-
    depends_of_db(H1, M1, _, Module2, Module1, 1),
    functor(H1, F1, A1),
    ( M1 \= Module1
    ->PI = M1:F1/A1
    ; PI = F1/A1
    ).

module_pred(D, Module1, Module2, Module2:PIL2, PIL1, PIL2) :-
    module_pred(D, Module1, Module2, PIL1, PIL2).

module_pred(D, Module1, Module2, PIL1, PIL2) :-
    findall(PI,
            ( member(PI1, PIL1),
              get_module_pred(D, Module1, Module2, PI1, PI)
            ), PIU2),
    sort(PIU2, PIL2).

get_module_pred(back, Module3, Module2, F3/A3, PI) :-
    % note we are ignoring M3:F3/A3, since they have no effect in dependencies
    functor(H3, F3, A3),
    depends_of_db(H2, M2, H3, Module3, Module2, _),
    functor(H2, F2, A2),
    ( M2 \= Module2
    ->PI = M2:F2/A2
    ; PI = F2/A2
    ).
get_module_pred(forw, Module1, Module2, PI1, F2/A2) :-
    ( PI1 = F1/A1
    ->M1 = Module1
    ; PI1 = M1:F1/A1
    ),
    functor(H1, F1, A1),
    depends_of_db(H1, M1, H2, Module2, Module1, _),
    functor(H2, F2, A2).

loop_to_chain(ModuleL1, ModuleL) :-
    last(ModuleL1, Last),
    ModuleL1 = [First|_],
    append([Last|ModuleL1], [First], ModuleL).

current_chain_link(ModuleL, Module1, Module2, Module3) :-
    append(_, [Module1, Module2, Module3|_], ModuleL).

pred_uses(M, PI, H) :-
    ( PI = M2:F2/A2
    ->true
    ; PI = F2/A2,
      M2 = M
    ),
    functor(H2, F2, A2),
    depends_of_db(H2, M2, H, M, M, _).

preds_uses(Module, PIL, RIL) :-
    findall(F/A,
            ( member(PI, PIL),
              pred_uses(Module, PI, H),
              functor(H, F, A)
            ), RIU, PIL),
    sort(RIU, RIL).

% Like module_uses/3 in [library(module_uses)], but using depends_of_db/6 database:

module_uses(LoadedIn, Module, Uses) :-
    findall(F/A, module_uses(LoadedIn, Module, F, A), Uses).

module_uses(LoadedIn, Module, F, A) :-
    distinct(H, depends_of_db(_, _, H, Module, LoadedIn, 1)),
    functor(H, F, A).
