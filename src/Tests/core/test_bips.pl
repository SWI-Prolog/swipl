/*  Part of SWI-Prolog

    Author:        Ulrich Neumerkel
    WWW:           http://www.swi-prolog.org
    Copyright (C): Ulrich Neumerkel

    This library is free software; you can redistribute it and/or
    modify it under the terms of the GNU Lesser General Public
    License as published by the Free Software Foundation; either
    version 2.1 of the License, or (at your option) any later version.

    This library is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
    Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public
    License along with this library; if not, write to the Free Software
    Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
*/

/** <module> Test built-in predicates

This module is a test-frame for testing built-in predicates.

*/

:- module(test_bips, [test_bips/0]).
:- use_module(library(plunit)).

test_bips :-
	run_tests([ bips,
		    bips_occurs_check_error,
		    arg,
		    eq,
		    length,
		    is_most_general_term
		  ]).

has_occurs_check_flag :-
	catch(current_prolog_flag(occurs_check, _), _, fail).


:- begin_tests(bips).

test(iso_8_3_10_4,[]) :-
       ground(3).
test(iso_8_3_10_4,[fail]) :-
       ground(a(1,_)).
test(iso_8_3_10, []) :-
       forall(between(0, 20, _),
              ( X=1,Y=2, ground(X-Y))).
test(iso_8_3_10, []) :-
       forall(true,ground(1-1)).
test(iso_8_3_10, [fail]) :-
       ground(1-1),
       fail.

test(iso_8_4_2_4,[Order == (<)]) :-
	compare(Order, 3, 5).
test(iso_8_4_2_4,[Order == (=)]) :-
	compare(Order, d, d).
test(iso_8_4_2_4,[Order == (=)]) :-
	compare(Order, d, d).
%test(iso_8_4_2_4,[Order == (>)]) :- % current disagreement
%	compare(Order, 3, 3.0).
test(iso_8_4_2_3_a,[error(type_error(atom, 1+1))]) :-
	compare(1+1, b, c).
test(iso_8_4_2_3_b,[error(domain_error(order, a))]) :-
	compare(a, b, c).
test(zero_codes, Order == (>)) :-
	compare(Order, '\u1000hello\u0000world', '\u1000hello').

null_file('/dev/null') :-
	exists_file('/dev/null'), !.
null_file(NullFile) :-
	source_location(_:null_file(_), ThisFile),
	file_directory_name(ThisFile, ThisDir),
	atom_concat(ThisDir, '/data/empty', NullFile).

test(iso_8_11_8, [ condition(null_file(Null)),
		   setup(open(Null, read, S)),
		   cleanup(close(S)),
		   ( Term, E ) == ( end_of_file, past )
		 ]) :- % Item#377
	stream_property(S, position(P)),
	set_stream_position(S, P),
	read(S, Term),
	stream_property(S, end_of_stream(E)).
test(iso_8_11_8, [ condition(null_file(Null)),
		   setup(open(Null, read, S)),
		   cleanup(close(S)),
		   E == at
		 ]) :-
	stream_property(S, end_of_stream(E)).

:- end_tests(bips).

:- begin_tests(bips_occurs_check_error,[condition(has_occurs_check_flag)]).

error_unification :-
	current_prolog_flag(occurs_check,error).

/* Item#310  PL_unify and occurs check error */
test(term_variable, [condition(error_unification),error(occurs_check(_, _))]) :-
	term_variables(GVars,GVars).
test(term_variable, [condition(error_unification),error(occurs_check(_, _))]) :-
	X = s(_),
	arg(1,X,X).
test(term_variable, [condition(error_unification),error(occurs_check(_, _))]) :-
	X =.. [s,X].
test(term_variable, [condition(error_unification),error(occurs_check(_, _))]) :-
	copy_term(X-X,Y-{Y}).
test(findall, [condition(error_unification),error(occurs_check(_,_))]) :-
	findall(X-X,true,[{X}-X]).
%test(clause, [condition(error_unification),error(occurs_check(_,_))]) :-
%	clause(equal(A,+A), _).
test(atom_to_term, [condition(error_unification),error(occurs_check(_,_))]) :-
	atom_to_term('X-X',X-{X},_).
test(sort,[condition(error_unification),error(occurs_check(_,_))]) :-
	sort([X,+X],[Y,Y]).

:- end_tests(bips_occurs_check_error).

:- begin_tests(arg).

test(shared, error(type_error(integer,a))) :-
	arg(a, f(a, b), a).
test(unify) :-
	arg(X, a(a(1,1), a(2,2)), a(X,2)).
test(zero, fail) :-
	arg(0, s(_), _).
test(one, X == Y) :-
	arg(1, s(X), Y).
test(two, fail) :-
	arg(2, s(_), _).
test(atom, error(type_error(integer, _))) :-
	arg(hello, s(_), _).
:- if(current_prolog_flag(bounded, false)).
test(big, fail) :-
	arg(1000000000000000000, s(_), _).
test(bigneg, error(domain_error(not_less_than_zero, _))) :-
	arg(-1000000000000000000, s(_), _).
:- endif.

test(arg_vf, L == [1]) :-		% By Edison Mera
    subterm_location(=(a), f(a), L).

subterm_location(Comparator, Term, []) :-
    call(Comparator, Term), !.
subterm_location(Comparator, Term, [N|L]) :-
    compound(Term),
    arg(N, Term, SubTerm),
    subterm_location(Comparator, SubTerm, L).

:- end_tests(arg).

:- begin_tests(eq).

:- style_check(-no_effect).
a :-
	A == A.
:- style_check(+no_effect).

test(eq_ff, true) :-
	a.

:- end_tests(eq).

:- begin_tests(length).

test(comp_len,[Length==3]) :-
	length([1, 2, 3], Length).
test(gen_list,[List =@= [_,_,_]]) :-
	length(List, 3).
test(neg_len,[error(domain_error(not_less_than_zero, -2))]) :-
	length(_List, -2).
test(gen_unbound,[all(List-Length =@= [[]-0, [_]-1, [_,_]-2])]) :-
	length(List,Length),
	( Length >= 2 -> ! ; true ).
test(no_integer,[error(type_error(integer,a))]) :-
	length(_, a).
test(no_integer,[error(type_error(integer,0.1))]) :-
	length(_, 0.1).
test(no_integer,[error(type_error(integer,-0.1))]) :-
	length(_, -0.1).
test(cycle,[sto(rational_trees),Length==3]) :-
	List = [List,List,List],
	length(List,Length).
test(expression,[error(type_error(integer,(1+2)))]) :-
	length(_,1+2).

/* disagreement with ISO */
test(no_list, [error(type_error(list,a))]) :-
	length(a,_).
test(no_list, [error(type_error(list,_))]) :-
	length([_,_|a],_).
test(no_list, [sto(rational_trees),error(type_error(list,List))]) :-
	List = [List,List,List|List],
	length(List, _).

test(swi, [ error(domain_error(not_less_than_zero, -300000000000000000)),
	    condition(current_prolog_flag(bounded, false))
	  ]) :- % Item#285
	length(_,-300000000000000000).


:- end_tests(length).

:- begin_tests(is_most_general_term).

test(not_callable, fail) :-
	is_most_general_term(1).
test(atom, true) :-
	is_most_general_term(a).
test(instantiated, fail) :-
	is_most_general_term(a(1)).
test(compound, true) :-
	is_most_general_term(a(_)).
test(compound, true) :-
	is_most_general_term(a(_,_)).
test(shared, fail) :-
	is_most_general_term(a(X,X)).
test(compound, fail) :-
	is_most_general_term(a(_,_,a)).
test(nil, true) :-
	is_most_general_term([]).
test(list, true) :-
	is_most_general_term([_]).
test(partial_list, fail) :-
	is_most_general_term([_|_]).
test(list, fail) :-
	is_most_general_term([_,a]).
test(shared, fail) :-
	is_most_general_term([_, Y, Y]).

:- end_tests(is_most_general_term).
