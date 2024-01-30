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

:- module(calls_to,
          [cleanup_calls_to/0,
           collect_calls_to/2,
           calls_to/1,
           calls_to/3,
           calls_to/4,
           calls_to_hook/4
          ]).

:- use_module(library(solution_sequences)).
:- use_module(library(option)).
:- use_module(library(lists)).
:- use_module(library(codewalk)).
:- use_module(library(location_utils)).
:- use_module(library(option_utils)).
:- use_module(library(compact_goal)).
:- use_module(library(compilation_module)).

:- init_expansors.

:- dynamic
    calls_to_public/2,
    calls_to_exported/2,
    calls_to_initialization/2,
    calls_to_assertion/4,
    calls_to_declaration/2,
    calls_to_clause/3,
    calls_to_predid/4.

:- multifile
    calls_to_hook/4.

cleanup_calls_to :-
    retractall(calls_to_public(_, _)),
    retractall(calls_to_exported(_, _)),
    retractall(calls_to_initialization(_, _)),
    retractall(calls_to_assertion(_, _, _, _)),
    retractall(calls_to_declaration(_, _)),
    retractall(calls_to_clause(_, _, _)),
    retractall(calls_to_predid(_, _, _, _)).

caller_ptr('<initialization>', _, '<initialization>') :- !.
caller_ptr('<assertion>'(AH),  _, '<assertion>'(AH) ) :- !.
caller_ptr('<declaration>',    _, '<declaration>'   ) :- !.
caller_ptr(_,        clause(Ptr), clause(Ptr)       ) :- !.
caller_ptr(M:H,                _, M:H).

record_calls_to(Type, Caller, Head, M, From) :-
    ( memberchk(Type, [use, lit])
    ->caller_ptr(Caller, From, Ptr),
      record_calls_to(Ptr, M, Head)
    ; true
    ).

record_calls_to('<public>',           M, Head) :- assertz(calls_to_public(           Head, M)).
record_calls_to('<exported>',         M, Head) :- assertz(calls_to_exported(         Head, M)).
record_calls_to('<initialization>',   M, Head) :- assertz(calls_to_initialization(   Head, M)).
record_calls_to('<assertion>'(AM:AH), M, Head) :- assertz(calls_to_assertion(AH, AM, Head, M)).
record_calls_to('<declaration>',      M, Head) :- assertz(calls_to_declaration(      Head, M)).
record_calls_to(clause(Ref),          M, Head) :- assertz(calls_to_clause(Ref,       Head, M)).
record_calls_to(CM:CH,                M, Head) :- assertz(calls_to_predid(CH, CM,    Head, M)).

calls_to('<public>'(M:H)     ) :- calls_to_public(H, M).
calls_to('<exported>'(M:H)   ) :- calls_to_exported(H, M).
calls_to('<initialization>'  ) :- once(calls_to_initialization(_, _)).
calls_to('<assertion>'(AM:AH)) :- distinct(AH:AM, calls_to_assertion(AH, AM, _, _)).
calls_to('<declaration>'     ) :- once(calls_to_declaration(_, _)).
calls_to(clause(Ref)         ) :- distinct(Ref, calls_to_clause(Ref, _, _)).
calls_to(CM:CH               ) :- distinct(CM:CH, calls_to_predid(CH, CM, _, _)).

calls_to(CRef, M, Head) :- calls_to(CRef, c, M, Head).

calls_to('<initialization>',   _, M, Head) :- calls_to_initialization(   Head, M).
calls_to('<assertion>'(AM:AH), _, M, Head) :- calls_to_assertion(AH, AM, Head, M).
calls_to('<declaration>',      _, M, Head) :- calls_to_declaration(      Head, M).
calls_to(clause(Ref),          _, M, Head) :- calls_to_clause(Ref,       Head, M).
calls_to(CM:CH,                W, M, Head) :- calls_to_predid(W, CH, CM, Head, M).

calls_to_predid(c, CH, CM, Head, M) :- calls_to_predid(CH, CM, Head, M).
calls_to_predid(w, CH, CM, Head, M) :-
    clause(calls_to:calls_to_predid(CH, CM,    _, _), _, Ref),
    clause(calls_to:calls_to_predid( _,  _, Head, M), _, Ref).

cu_caller_hook(Caller, Head, CM, Type, Goal, _, From) :-
    callable(Head),
    nonvar(CM),
    predicate_property(CM:Head, implementation_module(M)),
    ( Type \= lit
    ->compact_goal(Goal, Comp),
      record_location_goal(Head, M, Type, CM, Comp, From)
    ; Caller = '<assertion>'(A:H),
      member(Goal, [ foreign_props:fimport(_),
                     foreign_props:fimport(_, _),
                     foreign_props:tgen(_)
                   ])
    ->( A \= CM
      ->record_calls_to('<exported>', A, H)
      ; record_calls_to('<public>',   A, H)
      )
    ; true
    ),
    record_calls_to(Type, Caller, Head, CM, From),
    ( M \= CM
    ->record_calls_to('<exported>', M, Head)
    ; true
    ).

:- public collect_unused/4.
collect_unused(M, MGoal, Caller, From) :-
    record_location_meta(MGoal, M, From, all_call_refs, cu_caller_hook(Caller)).

:- public record_head_deps/2.
record_head_deps(Head, From) :-
    forall(calls_to_hook(Head, From, C, Called),
           ( predicate_property(C:Called, implementation_module(M)),
             record_calls_to(Head, C, Called),
             ( C \= M
             ->record_calls_to('<exported>', M, Called)
             ; true
             )
           )).

collect_calls_to(Options1, MFileD) :-
    foldl(select_option_default,
          [method(Method1)-clause],
          Options1, Options2),
    ( \+ memberchk(Method1, [prolog, clause]) % only these methods are supported
    ->Method = clause,
      print_message(
          warning,
          format("Method `~w' not supported yet, using `~w' instead",
                 [Method1, Method]))
    ; Method = Method1
    ),
    option(module(M), Options1, M),
    merge_options(Options2,
                  [source(false), % False, otherwise this will not work
                   method(Method),
                   on_trace(collect_unused(M)),
                   on_head(record_head_deps)
                  ], Options),
    option_module_files(Options, MFileD),
    walk_code([module_files(MFileD)|Options]).
