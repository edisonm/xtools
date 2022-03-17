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

:- module(dynamic_locations,
          [dynamic_locations/1,
           infer_dynl_if_required/0,
           infer_location_dynamic/3,
           inferred_dynl/0,
           cleanup_dynl_db/0
          ]).

:- use_module(library(option)).
:- use_module(library(location_utils)).
:- use_module(library(codewalk)).

:- dynamic
    inferred_dynl/0.

dynamic_locations(Options) :-
    option(module(M), Options, M), % Be careful, this is required to let M be
                                   % unified with the current module, specially
                                   % if method is prolog.
    walk_code([source(false), on_trace(collect_dynamic_locations(M))|Options]).

:- public collect_dynamic_locations/4.
collect_dynamic_locations(M, MGoal, _, From) :-
    record_location_dynamic(MGoal, M, From).

infer_dynl_if_required :-
    with_mutex(infer_dynl,
               ( \+ inferred_dynl
               ->dynamic_locations([infer_meta_predicates(false),
                                    autoload(false),
                                    evaluate(false),
                                    trace_reference(_),
                                    module_class([user, system, library])]),
                 assertz(inferred_dynl)
               ; true
               )).

cleanup_dynl_db :-
    cleanup_loc_dynamic(_, _, dynamic(_, _, _), _),
    retractall(inferred_dynl).

infer_location_dynamic(MGoal, M, From) :-
    ( \+ inferred_dynl
    ->record_location_dynamic(MGoal, M, From)
    ; true
    ).
