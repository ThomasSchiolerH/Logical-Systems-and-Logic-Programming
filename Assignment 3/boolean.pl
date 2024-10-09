% boolean.pl

:- op(650,xfy,eqv).  /* equivalence */ 
:- op(640,xfy,imp).  /* implication */ 
:- op(630,xfy,dis).  /* disjunction */ 
:- op(620,xfy,con).  /* conjunction */ 
:- op(610,fy, neg).  /* negation    */

tt(neg A,  V,TV) :- tt(A,V,TVA), negate(TVA,TV).
tt(A con B,V,TV) :- tt(A,V,TVA), tt(B,V,TVB), opr(con,TVA,TVB,TV).
tt(A dis B,V,TV) :- tt(A,V,TVA), tt(B,V,TVB), opr(dis,TVA,TVB,TV).
tt(A eqv B,V,TV) :- tt(A,V,TVA), tt(B,V,TVB), opr(eqv,TVA,TVB,TV).
tt(A imp B,V,TV) :- tt(A,V,TVA), tt(B,V,TVB), opr(imp,TVA,TVB,TV).
tt(A,      V,TV) :- member((A,TV),V).

negate(P,Q) :- P = t -> Q = f ; Q = t.

opr(con,P,Q,R) :- P = t, Q = t -> R = t ; R = f.
opr(dis,P,Q,R) :- P = f, Q = f -> R = f ; R = t.
opr(eqv,P,Q,R) :- P = Q -> R = t ; R = f.
opr(imp,P,Q,R) :- negate(P,N), opr(dis,N,Q,R).


% Question 1.2
boolean :-
    test_negate,
    test_opr.

% negate/2 predicate
test_negate :-
    negate(t, f),
    negate(f, t).

% opr/4 predicate
test_opr :-
    opr(con, t, t, t),
    opr(con, t, f, f),
    opr(con, f, t, f),
    opr(con, f, f, f),
    
    opr(dis, t, t, t),
    opr(dis, t, f, t),
    opr(dis, f, t, t),
    opr(dis, f, f, f),
    
    opr(eqv, t, t, t),
    opr(eqv, t, f, f),
    opr(eqv, f, t, f),
    opr(eqv, f, f, t),
    
    opr(imp, t, t, t),
    opr(imp, t, f, f),
    opr(imp, f, t, t),
    opr(imp, f, f, t).


% Question 1.3
values([t,f,x]).

negate1(P,Q) :-
  P = t -> Q = f ;
  P = f -> Q = t ;
  Q = P.

negate :-
  values(L), write(neg), nl,
  member(P,L), negate1(P,Q),
  write(P), write(' '), write(Q), nl,
  fail.
negate.

opr1(con, P, Q, R) :- 
    (P = t, Q = t -> R = t;
     P = f        -> R = f;
     Q = f        -> R = f;
     R = x).

opr1(dis, P, Q, R) :- 
    (P = t         -> R = t;
     Q = t         -> R = t;
     P = f, Q = f  -> R = f;
     R = x).

opr1(eqv, P, Q, R) :- 
    (P = Q -> R = t;   
     P = x -> R = x;   
     Q = x -> R = x;   
     R = f).           


opr1(imp, P, Q, R) :- 
    (P = t, Q = f -> R = f;
     P = t, Q = x -> R = x;
     P = x, Q = f -> R = x;
     R = t).


opr(Op) :-
    values(L), 
    write(Op), nl,
    member(P,L),
    member(Q,L),
    opr1(Op, P, Q, R),
    write(P), write(' '), write(Q), write(' '), write(R), nl,
    fail.
opr(_).