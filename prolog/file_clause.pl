/*  Part of Extended Tools for SWI-Prolog

    Author:        Edison Mera
    E-mail:        efmera@gmail.com
    WWW:           https://github.com/edisonm/xtools
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

:- module(file_clause,
          [ collect_file_clause_db/0,
            file_clause/4
          ]).

:- use_module(library(from_utils)).
:- use_module(library(list_sequence)).
:- use_module(library(track_deps)).
:- init_expansors.

% NOTE: don`t use table, since it is not working at expected:
% :- table file_clause/4 as (subsumptive, shared).

:- dynamic file_clause/4.
:- volatile file_clause/4.

:- meta_predicate file_clause(+,?,?,-).

% warm up table:
collect_file_clause_db :-
    with_mutex(collect_file_clause, do_collect_file_clause_db).

do_collect_file_clause_db :-
    retractall(file_clause(_, _, _, _)),
    forall(gen_file_clause(F, H, B, L),
           assertz(file_clause(F, H, B, L))).

match_head(Head, Head-Body) --> [Body].

gen_file_clause(File, MHead, Body, From) :-
    MHead = M:Head,
    From = clause(Ref),
    current_module(M),
    current_head(MHead),
    catch(clause(MHead, RTBody, Ref), _, fail),
    clause_property(Ref, module(CM)),
    from_to_file(From, File),
    from_to_line(From, Line),
    findall(Head-CTBody,
            head_calls_hook(Head, M, CTBody, File, Line),
            Pairs),
    foldl(match_head(Head), Pairs, List, [CM:RTBody]),
    list_sequence(List, Body).

current_head(MHead) :-
    current_predicate(_, MHead),
    \+ predicate_property(MHead, imported_from(_)),
    predicate_property(MHead, number_of_clauses(_)).
