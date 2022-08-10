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

:- module(module_loops, [module_loops/2]).

:- use_module(library(lists)).
:- use_module(library(solution_sequences)).
:- use_module(library(option_utils)).

skip_module(user).
skip_module(system).

:- dynamic
    loads_db/4.

update_loads(FileD) :-
    forall(( get_dict(File, FileD, _),
             module_property(Module, file(File)),
             '$load_context_module'(File, Context, _),
             \+ skip_module(Context),
             \+ loads_db(Context, Module, _, _)
           ),
           assertz(loads_db(Context, Module, [], 1))).

update_loads_dep :-
    update_loads_rec(1).

update_loads_rec(N1) :-
    succ(N1, N),
    forall(( loads_db(C, I, _, 1),
             loads_db(I, M, P1, N1),
             \+ loads_db(C, M, _, _)
           ),
           assertz(loads_db(C, M, [I|P1], N))),
    ( loads_db(_, _, _, N)
    ->update_loads_rec(N)
    ; true
    ).

%!  module_loops(-Loops, +Options) is det.
%
%   return the module loops, i.e., the module load chain that end up loading the
%   module itself.

module_loops(Loops, Options) :-
    option_files(Options, FileD),
    update_loads(FileD),
    update_loads_dep,
    findall(Loop,
            ( % this way to get the loop, allow us to see if there are several
              % paths between two nodes:
              loads_db(C, I, [], 1),
              loads_db(I, C, P2, _),
              normalize_loop([C, I|P2], Loop)
            ), List),
    sort(List, Loops).

normalize_loop(Loop, Norm) :-
    once(order_by([asc(Norm)],
                  ( append(Left, Right, Loop),
                    append(Right, Left, Norm)
                  ))).
