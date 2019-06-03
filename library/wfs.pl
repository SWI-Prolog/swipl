/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (c)  2019, VU University Amsterdam
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

:- module(wfs,
          [ undefined/0,

            call_residual_program/2,            % :Goal, -Clauses

            call_delays/2,                      % :Goal, -Delays
            delays_residual_program/2,          % +Delays, -Clauses
            answer_residual/2,                  % :Goal, :Residual

            op(900, fy, tnot)
          ]).
:- use_module(library(error)).
:- use_module(library(apply)).
:- use_module(library(lists)).

/** <module> Well Founded Semantics interface

The library(wfs) provides  the  user  interface   to  the  Well  Founded
Semantics (WFS) support in SWI-Prolog.
*/

:- meta_predicate
    call_delays(0, :),
    delays_residual_program(:, :),
    call_residual_program(0, :),
    answer_residual(:, :).

:- table
    undefined/0.

%!  undefined
%
%   Expresses the value _bottom_ from the well founded semantics.

undefined :-
    tnot(undefined).

%!  call_delays(:Goal, -Delays)
%
%   True when Goal is true with Delays.   Delays is `true` if the answer
%   is unconditionally true and a conjuctions   of tabled goals that are
%   _unknown_ according to the Well  Founded Semantics otherwise. Delays
%   only contains the unknown goals used for proving Goal. The predicate
%   call_delays/2  is  semantically  equivalent   to  call/1,  including
%   management of the delay list.

call_delays(Goal, Delays) :-
    '$wfs_call'(Goal, Delays).

%!  delays_residual_program(+Delays, -Clauses)
%
%   Given a delay as returned by call_delays/2, produce a set of clauses
%   the represents the complete residual   program responsible for these
%   delays, The program contains at least one loop through tnot/1 and is
%   either inconsistent or has multiple models   according to the stable
%   model semantics.

delays_residual_program(Delays, M:Clauses) :-
    phrase(residual_program(Delays, [], _), Program),
    maplist(unqualify_clause(M), Program, Clauses0),
    list_to_set(Clauses0, Clauses).

%!  call_residual_program(:Goal, -Clauses)
%
%   Call Goal and return the full residual program as a list of Clauses.

call_residual_program(Goal, M:Clauses) :-
    '$wfs_call'(Goal, 0:R0),                    % 0: leave qualified
    phrase(residual_program(R0, [], _), Program),
    maplist(unqualify_clause(M), Program, Clauses).

residual_program(true, Done, Done) -->
    !.
residual_program(_:true, Done, Done) -->
    !.
residual_program(G, Done, Done) -->
    { member(G2, Done),
      G2 =@= G
    }, !.
residual_program((A;B), Done0, Done) -->
    !,
    residual_program(A, Done0, Done1),
    residual_program(B, Done1, Done).
residual_program((A,B), Done0, Done) -->
    !,
    residual_program(A, Done0, Done1),
    residual_program(B, Done1, Done).
residual_program(tnot(A), Done0, Done) -->
    !,
    residual_program(A, Done0, Done).
residual_program(Goal0, Done0, Done) -->
    { (   predicate_property(Goal0, imported_from(M2))
      ->  Goal0 = _:G,
          Goal = M2:G
      ;   Goal = Goal0
      ),
      (   current_table(Goal, Trie)
      ->  true
      ;   '$tabling':more_general_table(Goal, Trie)
      ->  true
      ;   writeln(user_error, 'OOPS: Missing Call? '(Goal))
      ),
      '$tbl_table_status'(Trie, _Status, Goal, Skeleton),
      '$tbl_answer'(Trie, Skeleton, Condition)
    },
    [ (Goal :- Condition) ],
    residual_program(Condition, [Goal|Done0], Done).

unqualify_clause(M, (Head0 :- Body0), (Head :- Body)) :-
    unqualify(Head0, M, Head),
    unqualify(Body0, M, Body).

%!  answer_residual(:Goal, :Residual)
%
%   True when Goal resolves to a tabled   predicate  and Residual is the
%   _residual_ goal associated with an answer   for Goal. Residual is in
%   its most general form a disjunction   (;/2) of conjunctions (,/2) of
%   tabled goals.

answer_residual(Goal, M:Residual) :-
    predicate_property(Goal, tabled(_)),
    !,
    '$tbl_variant_table'(VariantTrie),
    trie_gen(VariantTrie, Goal, Trie),
    '$tbl_table_status'(Trie, _Status, Goal, Skeleton),
    '$tbl_answer'(Trie, Skeleton, Condition),
    unqualify(Condition, M, Residual).
answer_residual(Goal, _) :-
    permission_error(answer_residual, non_tabled_procedure, Goal).

unqualify((A0;B0), M, G) :-
    !,
    G = (A;B),
    unqualify(A0, M, A),
    unqualify(B0, M, B).
unqualify((A0,B0), M, G) :-
    !,
    G = (A,B),
    unqualify(A0, M, A),
    unqualify(B0, M, B).
unqualify(tnot(A0), M, G) :-
    !,
    G = tnot(A),
    unqualify(A0, M, A).
unqualify(M:G0, MG, G) :-
    '$c_current_predicate'(_, MG:G0),
    predicate_property(MG:G0, imported_from(M)),
    !,
    G = G0.
unqualify(M:G0, M, G) :-
    !,
    G = G0.
unqualify(G, _, G).
