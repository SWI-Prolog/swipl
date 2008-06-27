% Preliminary CLP(B) solver, based on CLP(FD)

:- module(clpb, [
                 op(300, fy, ~),
                 op(500, yfx, #),
                 sat/1,
                 taut/2,
                 labeling/1
                ]).

:- use_module(library(error)).
:- use_module(library(clpfd)).

parse_sat(V, V)   :- var(V), !, V in 0..1.
parse_sat(I, I)   :- integer(I), !.
parse_sat(~P0, V) :- parse_sat(P0, V0), V #= 1 - V0.
parse_sat(P*Q, V) :- parse_sat(P, VP), parse_sat(Q, VQ), V #= VP*VQ.
parse_sat(P+Q, V) :- parse_sat(P, VP), parse_sat(Q, VQ), V #= max(VP,VQ).
parse_sat(P#Q, V) :- parse_sat(P, VP), parse_sat(Q, VQ), V #= abs(VP-VQ).
parse_sat(X^P, V) :- parse_sat(P, V), V #<==> X #= 0 #\/ X #= 1.

sat_formula(V)       :- var(V), !.
sat_formula(I)       :- integer(I), !, memberchk(I, [0,1]).
sat_formula(~P)      :- sat_formula(P).
sat_formula(P*Q)     :- sat_formula(P), sat_formula(Q).
sat_formula(P+Q)     :- sat_formula(P), sat_formula(Q).
sat_formula(P#Q)     :- sat_formula(P), sat_formula(Q).
sat_formula(X^P)     :- var(X), sat_formula(P).
sat_formula(P=:=Q)   :- sat_formula(P), sat_formula(Q).
sat_formula(P =\= Q) :- sat_formula(P), sat_formula(Q).
sat_formula(P =< Q)  :- sat_formula(P), sat_formula(Q).
sat_formula(P >= Q)  :- sat_formula(P), sat_formula(Q).
sat_formula(P < Q)   :- sat_formula(P), sat_formula(Q).
sat_formula(P > Q)   :- sat_formula(P), sat_formula(Q).

% elementary
rewrite(V, V)            :- var(V), !.
rewrite(I, I)            :- integer(I).
rewrite(~P0, ~P)         :- rewrite(P0, P).
rewrite(P0*Q0, P*Q)      :- rewrite(P0, P), rewrite(Q0, Q).
rewrite(P0+Q0, P+Q)      :- rewrite(P0, P), rewrite(Q0, Q).
rewrite(P0#Q0, P#Q)      :- rewrite(P0, P), rewrite(Q0, Q).
rewrite(X^P0, X^P)       :- rewrite(P0, P).
% synonyms
rewrite(P0 =:= Q0, ~P # Q) :- rewrite(P0, P), rewrite(Q0, Q).
rewrite(P0 =\= Q0, P # Q)  :- rewrite(P0, P), rewrite(Q0, Q).
rewrite(P0 =< Q0, ~P + Q)  :- rewrite(P0, P), rewrite(Q0, Q).
rewrite(P0 >= Q0, P + ~Q)  :- rewrite(P0, P), rewrite(Q0, Q).
rewrite(P0 < Q0, ~P * Q)   :- rewrite(P0, P), rewrite(Q0, Q).
rewrite(P0 > Q0, P * ~Q)   :- rewrite(P0, P), rewrite(Q0, Q).


sat(Expr0) :-
        (   sat_formula(Expr0) -> true
        ;   domain_error(sat_expression, Expr0)
        ),
        rewrite(Expr0, Expr),
        parse_sat(Expr, 1),
        term_variables(Expr, Vs),
        \+ \+ label(Vs),
        attach_atts(Vs, Vs).

attach_atts([], _).
attach_atts([V|Vs], Vars) :-
        put_attr(V, clpb, Vars),
        attach_atts(Vs, Vars).

attr_unify_hook(Vars, Other) :-
        \+ \+ label(Vars),
        (   get_attr(Other, clpb, OVs) ->
            append(OVs, Vars, NVars),
            put_attr(Other, clpb, NVars)
        ;   true
        ).

attribute_goals(_) --> [].

taut(Expr0, Truth) :-
        (   sat_formula(Expr0) -> true
        ;   domain_error(sat_expression, Expr0)
        ),
        rewrite(Expr0, Expr),
        parse_sat(Expr, Var),
        term_variables(Expr, Vars),
        (   \+ \+ ( Var = 0, label(Vars)) ->
            \+ ( Var = 1, label(Vars)),
            Truth = 0
        ;   \+ \+ (Var = 1, label(Vars)),
            Truth = 1
        ).

labeling(Vs) :- label(Vs).
