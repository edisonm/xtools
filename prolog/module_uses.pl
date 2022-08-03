/*  Part of Extended Tools for SWI-Prolog

    Author:        Edison Mera
    E-mail:        efmera@gmail.com
    WWW:           https://github.com/edisonm/xtools
    Copyright (C): 2020, Process Design Center, Breda, The Netherlands.
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

:- module(module_uses,
          [ collect_module_uses/2,
            module_uses/2,
            module_uses/3,
            module_uses/4
          ]).

:- use_module(library(codewalk)).

:- meta_predicate
    collect_module_uses(+,0,+,+).

:- dynamic module_uses/4.

module_uses(LoadedIn, Module, Uses) :-
    collect_module_uses(LoadedIn, Module:_),
    module_uses_2(m(LoadedIn, Module), Uses).

module_uses(LoadedIn, Uses) :-
    collect_module_uses(LoadedIn, _),
    module_uses_2(all(LoadedIn), Uses).

module_uses(Uses) :-
    collect_module_uses(_, _),
    module_uses_2(all, Uses).

pattern(m(_, M), _-(M:F/A),  F/A).
pattern(all(_),       _-PI,   PI).
pattern(all,          Pair, Pair).

collect_module_uses(LoadedIn, TR) :-
    walk_code([module(LoadedIn),
               source(false),
               method(clause),
               trace_reference(TR),
               on_trace(collect_module_uses(LoadedIn))
              ]).

module_uses_2(Collector, Uses) :-
    pattern(Collector, LoadedIn-(M:F/A), Pattern),
    findall(Pattern, module_uses(LoadedIn, M, F, A), UsesU),
    sort(UsesU, Uses).

:- public
    collect_module_uses/4.

collect_module_uses(LoadedIn, MGoal, _, _) :-
    strip_module(MGoal, _, Goal),
    functor(Goal, F, A),
    predicate_property(MGoal, implementation_module(Module)),
    LoadedIn \= Module,
    assertz(module_uses(LoadedIn, Module, F, A)).
