/*  Part of Extended Tools for SWI-Prolog

    Author:        Edison Mera
    E-mail:        efmera@gmail.com
    WWW:           https://github.com/edisonm/xtools
    Copyright (C): 2024, Process Design Center, Breda, The Netherlands.
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

:- module(clause_indicator,
          [ clause_indicator//2
          ]).

:- use_module(library(prolog_clause)).

clause_indicator(clause_term_position(Ref, _),  _) --> {nonvar(Ref)}, !, clause_ref_indicator(Ref).
clause_indicator(clause(Ref),                   _) --> {nonvar(Ref)}, !, clause_ref_indicator(Ref).
clause_indicator(file_term_position(_, _), Caller) --> caller_indicator(Caller).
clause_indicator(file(_, _, _, _),         Caller) --> caller_indicator(Caller).

clause_ref_indicator(Ref) -->
    { nth_clause(Head, I, Ref),
      strip_module(Head, M, Pred),
      functor(Pred, F, A)
    },
    ["~w"-[M:F/A-I]].

caller_indicator('<initialization>' ) --> ['(initialization)'].
caller_indicator('<declaration>'    ) --> ['(declaration)'].
caller_indicator('<assertion>'(Pred)) -->
    {predicate_name(Pred, Name)},
    ["~w (assertion)"-[Name]].
caller_indicator(Pred) -->
    {predicate_name(Pred, Name)},
    [Name].

