/*  Part of Extended Tools for SWI-Prolog

    Author:        Edison Mera
    E-mail:        efmera@gmail.com
    WWW:           https://github.com/edisonm/xtools
    Copyright (C): 2015, Process Design Center, Breda, The Netherlands.
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

:- module(mark_preds,
          [ cleanup_marked/0,
            gen_lit_marks/2,
            marked/1,
            match_head_clause/2,
            mark_compile_time_called/0,
            put_mark/1
          ]).

:- use_module(library(qualify_meta_goal)).
:- use_module(library(calls_to)).
:- use_module(library(compilation_module)).
:- use_module(library(solution_sequences)).
:- init_expansors.

:- dynamic
    marked_assertion/2,
    marked_predid/2,
    marked_clause/1,
    marked_initialization/0,
    marked_declaration/0,
    marked_exported/2.

cleanup_marked :-
    retractall(marked_clause(_)),
    retractall(marked_assertion(_, _)),
    retractall(marked_predid(_, _)),
    retractall(marked_initialization),
    retractall(marked_declaration),
    retractall(marked_exported(_, _)).

marked('<assertion>'(M:H)) :- marked_assertion(H, M).
marked('<public>'(M:H))    :- marked_predid(H, M).
marked(M:H)                :- marked_predid(H, M).
marked(clause(Ref))        :- marked_clause(Ref).
marked('<initialization>') :- marked_initialization.
marked('<declaration>')    :- marked_declaration.
marked('<exported>'(M:H))  :- marked_exported(H, M).

record_marked('<assertion>'(M:H)) :- assertz(marked_assertion(H, M)).
record_marked('<public>'(M:H))    :- assertz(marked_predid(H, M)).
record_marked(M:H)                :- assertz(marked_predid(H, M)).
record_marked(clause(Ref))        :- assertz(marked_clause(Ref)).
record_marked('<initialization>') :- assertz(marked_initialization).
record_marked('<declaration>'   ) :- assertz(marked_declaration).
record_marked('<exported>'(M:H) ) :- assertz(marked_exported(H, M)).

resolve_meta_goal(H, M, G) :-
    ( ( predicate_property(M:H, meta_predicate(Meta))
                                % don`t use inferred_meta_predicate(M:H, Meta)
                                % since actually it is not being used by the
                                % compiler and would lead to incorrect results
      )
    ->qualify_meta_goal(M:H, Meta, G)
    ; G = H
    ).

is_marked(CRef) :-
    copy_term(CRef, Term),
    marked(Term),
    subsumes_term(Term, CRef).

check_and_mark(CRef) :-
    \+ is_marked(CRef),
    record_marked(CRef).

put_mark(CRef) :-
    ( with_mutex(check_and_mark, check_and_mark(CRef))
    ->forall(( calls_to(CRef, w, CM, Callee),
               strip_module(CM:Callee, M, H),
               predicate_property(M:H, implementation_module(IM))
             ),
             mark_rec(H, IM))
    ; true
    ).

mark_rec(H, M) :-
    resolve_meta_goal(H, M, G),
    forall(gen_lit_marks(M:G, CRef), % Widening
           put_mark(CRef)).

:- meta_predicate gen_lit_marks(0, ?).

%!  gen_lit_marks(:Goal, Ref)
%
%   Generalization step, we lose precision but avoid loops --EMM
%
%   The order of this clauses matters, because we record as marked from the most
%   specific to the most generic one !!!
%
%   The logic is: a call to a predicate will potentially use:
%
%   (1) all the assertions
%   (2) the clauses that match, and
%   (3) the dynamic calls that match

gen_lit_marks(M:G, '<assertion>'(M:P)) :-
    functor(G, F, A),
    functor(P, F, A).          % Build a fresh head without undesirable bindings
gen_lit_marks(MG, clause(Clause)) :-
    match_head_clause(MG, Clause),
    clause_property(Clause, file(_)).    % Static clauses only
gen_lit_marks(G, P) :- copy_term(G, P). % copy term to avoid undesirable bindings

:- meta_predicate match_head_clause(0, -).
match_head_clause(MH, Clause) :-
    catch(clause(MH, _, Clause), _, fail).

mark_compile_time_called :-
    forall(distinct(M:H,
                    ( compile_time_called(H, M, C),
                      M \= C
                    )),
           put_mark('<exported>'(M:H))).

