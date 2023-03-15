/*  Part of Extended Tools for SWI-Prolog

    Author:        Edison Mera
    E-mail:        efmera@gmail.com
    WWW:           https://github.com/edisonm/xtools
    Copyright (C): 2013, Process Design Center, Breda, The Netherlands.
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

:- module(module_files,
          [ module_file/2,
            module_files/2,
            file_module/2,
            file_modules/2
          ]).

:- use_module(library(solution_sequences)).

% NOTE: Files are not unique, and the first must be the main one
module_files(M, Files) :-
    findall(File, distinct(File, module_file(M, File)), Files).

file_modules(File, ML) :-
    findall(M, distinct(M, file_module(M, File)), ML).

module_file_1(M, File) :-
    module_property(M, file(File)).
module_file_1(M, File) :-
    '$load_context_module'(File, M, _),
    \+ module_property(_, file(File)).

%!  module_file(+Module, -File) is multi.

module_file(M, File) :-
    module_file_rec(module_file_1, M, File).

module_file_rec(GetFile, M, File) :-
    SC = s(fail),
    ( call(GetFile, M, File),
      nb_setarg(1, SC, true)
    ; SC = s(true),
      module_file_rec(get_incl_file(GetFile), M, File)
    ).

get_incl_file(GetFile, M, Incl) :-
    distinct(Incl,
             ( call(GetFile, M, File1),
               source_file_property(File1, includes(Incl, _))
             )).

%!  file_module(+File, -Module) is multi.

file_module(File, M) :-
    (   distinct(File1, source_file_property(File1, includes(File, _)))
    *-> file_module(File1, M)
    ;   module_file_1(M, File)
    ).
