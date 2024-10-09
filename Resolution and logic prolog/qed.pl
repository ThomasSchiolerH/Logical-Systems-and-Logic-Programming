% qed.pl

%
% QED - First-Order Logic
%

resolve(S) :- member([], S), !.
resolve(S) :-
  member(C1, S), member(C2, S), C1 \== C2,               
  copy_term(C2, C2_R),
  clashing(C1, L1, C2_R, L2, Subst),
  delete_lit(C1, L1, Subst, C1P),
  delete_lit(C2_R, L2, Subst, C2P),
  clause_union(C1P, C2P, Resolvent),
  \+ clashing(Resolvent, _, Resolvent, _, _),
  \+ member(Resolvent, S),
  copy_term((C1,C2_R,Subst), Result),
  numbervars(Result, 1, _, [functor_name(x)]),
  write_result(Result), nl,
  write_clauses([Resolvent | S]), nl,
  resolve([Resolvent | S]).

write_result((C1,C2_R,Subst)) :-
  nl,
  write('Resolve '), write_clauses([C1]), nl,
  write('  and   '), write_clauses([C2_R]), nl,
  nl,
  write_eq_list(Subst).

%
%  Unification algorithm by Martelli/Montanari.
%

test_unify(A, B) :-
  unify(A, B, Subst),
  nl,
  write_unified(A, B, Subst)
  -> fail.
test_unify(_, _).

%
%  Skolemize a formula.
%

 
  
dump_cnf(A, A5) :-
  dump(A),
  rename(A, A1), dump(A1),
  eliminate(A1, A2), dump(A2),
  demorgan(A2, A3), dump(A3),
  extract(A3, A4), dump(A4),
  distribute(A4, A5), dump(A5).

dump(A) :-
  to_external(A, A1),
  write_formula(A1), nl.

%
%  Logical operators
%

%
%  Alphabetic operators for internal use
%
:- op(650, xfy, dif).  /* difference  */
:- op(650, xfy, eqv).  /* equivalence */
:- op(640, xfy, imp).  /* implication */
:- op(630, xfy, dis).  /* disjunction */
:- op(620, xfy, con).  /* conjunction */
:- op(610, fy,  neg).  /* negation    */

:- op(600, xfy, eq).   /* equality    */

:- op(610, fy,  always).     /* always     */ 
:- op(610, fy,  eventually). /* eventually */ 
:- op(610, fy,  next).       /* next       */ 

%
%  Symbolic operators for external use
%
:- op(650, xfy, \<=>). /* difference  */
:- op(650, xfy, <=>).  /* equivalence */
:- op(640, xfy, =>).   /* implication */
:- op(630, xfy, \).    /* disjunction */
:- op(620, xfy, &).    /* conjunction */
:- op(610, fy,  ~).    /* negation    */

%:- op(610, fy, #).     /* always     */ 
%:- op(610, fy, <>).    /* eventually */ 
%:- op(610, fy, @).     /* next       */ 

%
% Syntactic and semantic definitions of symbols
%

%
%  Translation between operator symbols
%
symbol_opr(\<=>, dif). /* difference  */
symbol_opr(<=>,  eqv). /* equivalence */
symbol_opr(=>,   imp). /* implication */
symbol_opr(\,    dis). /* disjunction */
symbol_opr(&,    con). /* conjunction */
symbol_opr(~,    neg). /* negation    */

symbol_opr(# ,   always).
symbol_opr(<> ,  eventually).
symbol_opr(@ ,   next).

%
%  Transform a formula to CNF
%

%
%  cnf(A, B)
%    B is A in conjunctive normal form.
%
cnf(A, A5) :-
  rename(A, A1),           % Needed only for predicate formulas
  eliminate(A1, A2), 
  demorgan(A2, A3),
  extract(A3, A4),         % Needed only for predicate formulas
  distribute(A4, A5).

%
%  rename(A, B)
%  rename(A, List, Num, B)
%    B is A with bound variables renamed.
%    List is a list of pairs (X, Y),
%      where the Xs are all the variables,
%      and Y is X for the first occurrence of X
%      or a new variable for subsequent occurrences.
%    List1 is List appended with new substitutions created.
%
rename(A, B) :- rename(A, [], _, B).

rename(all(X, A), List, List1, all(Y, A1)) :-
  member_var((X, _), List), !,       % The variable was already encountered.
  copy_term(X, Y),                   % Create a new variable.
  rename(A, [(X, Y) | List], List1, A1).

rename(all(X, A), List, List1, all(X, A1)) :- !,
  rename(A, [(X, X) | List], List1, A1).
                                     % First occurrence "replaced" by itself.
rename(ex(X, A), List, List1, ex(Y, A1)) :-
  member_var((X, _), List), !,
  copy_term(X, Y),
  rename(A, [(X, Y) | List], List1, A1).
rename(ex(X, A), List, List1, ex(X, A1)) :- !, 
  rename(A, [(X, X) | List], List1, A1).
                                     % Similarly for ex quantifier.
rename(A, List, List2, B) :-
  A =.. [Opr, A1, A2],
  symbol_opr(_, Opr), !,
  rename(A1, List, List1, B1),
  rename(A2, List1, List2, B2),
  B =.. [Opr, B1, B2].

rename(neg A, List, List1, neg B) :- !,
  rename(A, List, List1, B).
rename(A, List, List, B) :-
  A =.. [F | Vars],
  subst_var(Vars, Vars1, List),
  B =.. [F | Vars1].

%
%  member_var((X,Y), List)
%    Finds the first pair (X,Y) in List.
%    Called with X bound to a variable and Y not bound.
%
member_var((A,Y), [(B,Y) | _]) :- A == B, !.
member_var(A, [_ | C]) :- member_var(A, C).

%
%  subst_var(V1List, V2List, List)
%    V1List is a list of variables, and List is a list of variable pairs.
%    For X in V1List, the corresponding element in V2List is Y,
%      if (X,Y) is in List, otherwise, it is X.
%  (The third clause is used in skolem, not in cnf.)
%
subst_var([], [], _).
subst_var([V | Tail], [V1 | Tail1], List) :-
  member_var((V, V1), List), !,
  subst_var(Tail, Tail1, List).
subst_var([V | Tail], [V | Tail1], List) :-
  subst_var(Tail, Tail1, List).

%
%  extract(A, B)
%    B is A with quantifiers extracted to prefix.
%
extract(all(X,A), all(X,A1)) :- !, extract(A, A1).
extract(ex(X,A), ex(X,A1)) :- !, extract(A, A1).

extract(all(X, A) dis B, all(X, C)) :- !, extract(A dis B, C).
extract(ex(X,  A) dis B, ex(X,  C)) :- !, extract(A dis B, C).
extract(all(X, A) con B, all(X, C)) :- !, extract(A con B, C).
extract(ex(X,  A) con B, ex(X,  C)) :- !, extract(A con B, C).

extract(A dis all(X, B), all(X, C)) :- !, extract(A dis B, C).
extract(A dis ex(X,  B), ex(X,  C)) :- !, extract(A dis B, C).
extract(A con all(X, B), all(X, C)) :- !, extract(A con B, C).
extract(A con ex(X,  B), ex(X,  C)) :- !, extract(A con B, C).

extract(A dis B, C) :- !,
  extract(A, A1),
  extract(B, B1),
  (is_quantified(A1, B1) -> extract(A1 dis B1, C) ; (C = A dis B) ).

extract(A con B, C) :- !,
  extract(A, A1),
  extract(B, B1),
  (is_quantified(A1, B1) -> extract(A1 con B1, C) ; (C = A con B) ).

extract(A, A).

is_quantified(ex(_,_),  _).
is_quantified(all(_,_), _).
is_quantified(_, ex(_,_)).
is_quantified(_, all(_,_)).

%
%  eliminate(A, B)
%    B is A without eqv, dif and imp.
%
eliminate(A eqv B,
          (A1 con B1) dis ((neg A1) con (neg B1)) ) :- !,
  eliminate(A, A1),
  eliminate(B, B1).
eliminate(A dif B,
          (A1 con (neg B1)) dis ((neg A1) con B1) ) :- !,
  eliminate(A, A1),
  eliminate(B, B1).
eliminate(A imp B,
          (neg A1) dis B1 ) :- !,
  eliminate(A, A1),
  eliminate(B, B1).
eliminate(A dis B, A1 dis B1) :- !,
  eliminate(A, A1),
  eliminate(B, B1).
eliminate(A con B, A1 con B1) :- !,
  eliminate(A, A1),
  eliminate(B, B1).
eliminate(neg A, neg A1) :- !,
  eliminate(A, A1).
eliminate(all(X,A), all(X,A1)) :- !,
  eliminate(A, A1).
eliminate(ex(X,A), ex(X,A1)) :- !,
  eliminate(A, A1).
eliminate(A, A).

%
%  demorgan(A, B)
%    B is A with negations pushed inwards and
%    reducing double negations.
%
demorgan(neg (A con B), A1 dis B1) :- !,
  demorgan(neg A, A1),
  demorgan(neg B, B1).
demorgan(neg (A dis B), A1 con B1) :- !,
  demorgan(neg A, A1),
  demorgan(neg B, B1).
demorgan((neg (neg A)), A1) :- !,
  demorgan(A, A1).
demorgan(neg all(X,A), ex(X,A1)) :- !,
  demorgan(neg A, A1).
demorgan(neg ex(X,A), all(X,A1)) :- !,
  demorgan(neg A, A1).

demorgan(neg always A, eventually A1) :- !,
  demorgan(neg A, A1).
demorgan(neg eventually A, always A1) :- !,
  demorgan(neg A, A1).

demorgan(all(X,A), all(X,A1)) :- !,
  demorgan(A, A1).
demorgan(ex(X,A), ex(X,A1)) :- !,
  demorgan(A, A1).
demorgan(A con B, A1 con B1) :- !,
  demorgan(A, A1),
  demorgan(B, B1).
demorgan(A dis B, A1 dis B1) :- !,
  demorgan(A, A1),
  demorgan(B, B1).
demorgan(A, A).

%
%  distribute(A, B)
%    B is A with disjuntion distributed over conjunction.
%
distribute(all(X,A), all(X,A1)) :- !, distribute(A, A1).
distribute(ex(X,A),  ex(X,A1))  :- !, distribute(A, A1).
distribute(A con B, A1 con B1) :- !,
  distribute(A, A1),
  distribute(B, B1).
distribute(A dis B, AB) :- !,
  distribute(A, A1),
  distribute(B, B1),
  distribute(A1, B1, AB).
distribute(A, A).

distribute(A con B, C, D) :- !,
  D = D1 con D2,
  distribute(A, C, D1),
  distribute(B, C, D2).
distribute(C, A con B, D) :- !,
  D = D1 con D2,
  distribute(C, A, D1),
  distribute(C, B, D2).
distribute(A, B, A dis B).

%
%  cnf_to_clausal(A, S)
%    A is a CNF formula, S is the formula in clausal notation.
%
cnf_to_clausal(A1 con A2, S) :- !,
  cnf_to_clausal(A1, S1),
  cnf_to_clausal(A2, S2),
  union_term(S1, S2, S).
cnf_to_clausal(A, S) :-
  disjunction_to_clausal(A, S).

disjunction_to_clausal(A, S) :-
  disjunction_to_clause(A, C),
  ( member(L1, C), member(neg L2, C), L1 == L2 ->
    S = []
  ;
    S = [C]
  ).

disjunction_to_clause(A1 dis A2, S) :- !,
  disjunction_to_clause(A1, S1),
  disjunction_to_clause(A2, S2),
  union_term(S1, S2, S).
disjunction_to_clause(A, [A]).

union_term([],L,L) :- !.
union_term([H|T],L,R) :-
  member_term(H,L), !, 
  union_term(T,L,R).
union_term([H|T],L,[H|R]) :-
  union_term(T,L,R).

%
%  member_term(T, List) - Like member, but do not unify.
%
member_term(L, [Head|_]) :-
  L == Head, !.
member_term(L, [_|Tail]) :- !,
  member_term(L, Tail).

%
% IO
%

%
%  term_length(T, L) - L is the length of term T
%
term_length(T, L) :-
  term_to_atom(T, A),
  string_to_atom(S, A),
  string_length(S, L).

%
%  fieldl(T, N) - write term T left  justified in a field of length T
%  fieldr(T, N) - write term T right justified in a field of length T
%
fieldl(T, N) :-
  write(T),
  term_length(T, L),
  Spaces is N - L,
  tab(Spaces).

fieldr(T, N) :-
  term_length(T, L),
  Spaces is N - L,
  tab(Spaces),
  write(T).

%
%  write_tt_title(Fml, Atoms)
%    write the truth table title: formula and atoms
%
write_tt_title(Fml, Atoms) :-
  to_external(Fml, EFml),
  write(EFml),
  write('  '),
  write_tt_title1(Atoms).

write_tt_title1([A|Tail]) :-
  write(A),
  write(' '),
  write_tt_title1(Tail).
write_tt_title1([]) :-
  write(' value '), nl.

%
%  write_tt_line(Fml, V, TV)
%    write a truth table line,
%    Fml is a formula (used for indenting)
%    V a valuation and TV the truth value
%
write_tt_line(Fml, V, TV) :-
  to_external(Fml, EFml),
  term_length(EFml, L),
  tab(L),
  write('  '),
  write_valuation(V),
  write('   '),
  write(TV),
  nl.

%
%  write_valuation(List)
%    write the valuations in the List with blank separators
%
write_valuation([]).                                                                       
write_valuation([(_,TV)|Tail]) :-
  write(TV),
  write(' '),
  write_valuation(Tail).

%
%  write_proof_line(Line, A, Reason)
%    A is the Line'th line of the proof for Reason.
%
write_proof_line(Line, Fml, Reason) :-
  fieldr(Line, 3),
  write('.'),
  Fml = deduce(Assump, A),
  write_formula_list(Assump),
  write(' |- '),
  to_external(A, E),
  write_formula(E),
  line_position(user_output, Pos),
  Spaces = 60 - Pos,
  tab(Spaces),
  write_list(Reason), nl.

%
%  write_formula(Fml) - write the formula Fml.
%
write_formula(Fml) :-
  copy_term(Fml, Fml1),          % Do not instantiate original formula.
  numbervars(Fml1, 1, _, [functor_name(x)]),     % Instantiate variables for output.
  write_formula1(Fml1).
  
write_formula1(all(X, A)) :- !,
  write('A'),
  write_term(X),
  write_formula1(A).
write_formula1(ex(X, A))  :- !,
  write('E'),
  write_term(X),
  write_formula1(A).
write_formula1(Fml) :-
  Fml =.. [Opr, A, B],
  symbol_opr(Opr, _), !,
  write_formula2(Opr, A, B).
write_formula1(Fml) :-
  Fml =.. [Opr, A],
  symbol_opr(Opr, _), !,
  write(Opr),
  write_formula1(A).
write_formula1(A) :-
  atom(A), !,
  write(A).
write_formula1(A) :-
  A =.. [F | Vars],
  write(F), write('('),
  write_subterms(Vars),
  write(')').

%
%  write_formula2(Fml) - add parentheses for binary formulas
%
write_formula2(Op, A, B) :-
  write('('), write_formula1(A), write(' '),
  write(Op),
  write(' '), write_formula1(B), write(')').

%
%  write_term(T)        - write the term T
%  write_subterms(List) - write the list of subterms
%
write_term(T) :-
  atom(T), !,
  write(T).
write_term(x(N)) :- !,
  write('x'), write(N).
write_term(T) :-
  T =.. [F | Subterms],
  write_term(F),
  write('('),
  write_subterms(Subterms),
  write(')').
write_term(T) :- write(T).

write_subterms(List) :- write_comma_list(write_term, List).

%
%  write_list(List) - write a list
%
write_list(List) :- checklist(write, List).

%
%  write_comma_list(Pred, List)
%    Write the elements of List with comma separators.
%    The elements are written by Pred.
%
write_comma_list(Pred, [T1, T2 | Tail]) :-
  call(Pred, T1),
  write(','),
  write_comma_list(Pred, [T2 | Tail]).
write_comma_list(Pred, [T]) :-
  call(Pred, T).
write_comma_list(_, []).

%
%  write_formula_list - write list of formula separated by commas
%
write_formula_list(List) :-
  to_external_list(List, ListE),
  write_comma_list(write_formula, ListE).

%
%  write_tableau(Tab)
%  write_tableau(Tab, Indent, Line)
%    Write tableau Tab, Indenting each level of the tree,
%      with line number Line (currently only for temporal logic).
%  write_formula_list(Fml)
%    Write the list of formulas Fml.
% 
write_tableau(Tab) :-
  write_tableau(Tab, 0, 0).

write_tableau(empty,_,_).
write_tableau(closed,_,_) :- 
  write(' Closed').
write_tableau(open,_,_)   :- 
  write(' Open  ').
write_tableau(connect(N),_,_) :-
  write(' Connect to '), write(N).
write_tableau(t(Fmls, Left, Right), Indent, N) :-
  nl,
  ( (N =\= 0) -> (fieldr(N, 3), write('  ')) ; true),
  tab(Indent), Indent1 is Indent + 3,
  write_formula_list(Fmls),
  write_tableau(Left, Indent1, N),
  write_tableau(Right, Indent1, N).

%
%  Clause for predicate calculus with extra field.
%
write_tableau(t(Fmls, Left, Right, _), Indent, N) :-
  write_tableau(t(Fmls, Left, Right), Indent, N).

%
%  Clause for temporal logic with extra fields.
%
write_tableau(t(Fmls, Left, Right, N, _), Indent, _) :-
  write_tableau(t(Fmls, Left, Right), Indent, N).

%
%  write_clauses(List) - write a list of clauses
%  write_clauses - writes an empty list as []
%    and passes non-empty lists to write_clause1
%
write_clauses([]) :-
  write('[]').
write_clauses(List) :-
  copy_term(List, List1),          % Do not instantiate original formula.
  numbervars(List1, 1, _, [functor_name(x)]),     % Instantiate variables for output.
  write_clauses1(List1).

write_clauses1([]).
write_clauses1([H|T]) :-
  to_external_list(H, HE),
  write('['),
  write_clause(HE),
  write(']'),
  write_clauses1(T).

write_clause([]).         % for empty clause
write_clause([H]) :-      % don't append comma after last element
  !,
  write_formula(H).
write_clause([H|T]) :-
  write_formula(H),
  write(','),
  write_clause(T).

write_unified(L1, L2, Subst) :-
  numbervars((L1, L2), 1, _, [functor_name(x)]),
  write('Unify '), write_formula(L1), nl,
  write(' and  '), write_formula(L2), nl,
  nl,
  write_solved(Subst).

write_solved([failure3 | E]) :- !,
  write('Failed (different functors) in '), nl,
  write_eq_list(E).
write_solved([failure4 | E]) :- !,
  write('Failed (occurs check) in '), nl,
  write_eq_list(E).
write_solved(L) :-
  write_eq_list(L).

write_eq_list(List) :- checklist(write_eq, List).

write_eq(T1 eq T2) :-
  write_term(T1), write(' = '), write_term(T2), nl.

%
%  write_tl_tableau -
%    Write the various elements of the tableau construction.
%  write_tau(T) -
%    Write a new line after each transition tau
%  write_tableau_result -
%    Write the result: un/satisfiable or need to check fulfilment.
%
write_tl_tableau(Tab, States, Tau, Tab_Result) :-
  write_tableau(Tab),   nl, nl,
  write_states(States), nl,
  checklist(write_tau, Tau), nl,
  write_tableau_result(Tab_Result).

write_tau(T) :- write(T), nl.

write_tableau_result(open)    :- write('Formula is satisfiable  '), nl.
write_tableau_result(closed)  :- write('Formula is unsatisfiable'), nl.
write_tableau_result(connect) :- write('Checking fulfilment.....'), nl.

%
%  write_states(List)
%    Write the List of states.
%
write_states([]).
write_states([st(Fmls,N)|Tail]) :- 
  write('State '), write(N), write(' '), nl, write('  '),
  write_formula_list(Fmls), nl, 
  write_states(Tail).

%
%  write_fulfil
%    Write the results of the fulfilment check at a connect node:
%      the SCCs and Edges
%  write_fulfil1/write_fulfil2
%    For each node, write if it is fulfiling and if not, for which formula.
%  write_fulfil_result
%    Write open if fulfiling or closed.
%
write_fulfil(connect, SCCs, Edges, Fulfil_Result) :-
  write('SCCs = '),  write(SCCs), nl,
  write('Edges = '), write(Edges), nl,
  write_fulfil1(Fulfil_Result),
  write_fulfil_result(Fulfil_Result).
write_fulfil(_, _, _, _).

write_fulfil1([Head|Tail]) :-
  write_fulfil2(Head),
  write_fulfil1(Tail).
write_fulfil1([]).

write_fulfil2(none) :- !.
write_fulfil2(ok(S))   :- !,
  write(S), write(' is fulfilling'), nl.
write_fulfil2(notok(S,F)) :- !,
  write(S), write(' is not fulfilling for '),
  to_external(F, FE),
  write_formula(FE), nl.

write_fulfil_result(R) :-
  member(ok(_), R), !,
  write_tableau_result(open).
write_fulfil_result(_) :-
  write_tableau_result(closed).

%
% Translates internal to external symbols and conversely
%

%
%  to_external(Int, Ext) -
%    translates Int in internal format to Ext in external format
%
to_external(ex(X,Fml),  ex(X,EFml))  :- !,
  to_external(Fml, EFml). 
to_external(all(X,Fml), all(X,EFml)) :- !,
  to_external(Fml, EFml).
to_external(Fml, Ext) :-
  Fml =.. [Opr, F1, F2],       % decompose binary formula
  symbol_opr(Sym, Opr), !,     % get symbol
  to_external(F1, E1),         % recurse on subformulas
  to_external(F2, E2),
  Ext =.. [Sym, E1, E2].       % recompose formulas
to_external(Fml, Ext) :-
  Fml =.. [Opr , F],           % similarly for unary formula
  symbol_opr(Sym, Opr), !,
  to_external(F, E),
  Ext =.. [Sym, E].
to_external(F, F).

%
%  to_internal(Ext, Int) -
%    translates Ext in external format to  Int in internal format
%
to_internal(ex(X,Fml),  ex(X,IFml)) :- !,
  to_internal(Fml, IFml).
to_internal(all(X,Fml), all(X,IFml)) :- !,
  to_internal(Fml, IFml).
to_internal(Fml, Int) :-
  Fml =.. [Sym, F1, F2],      % decompose binary formula
  symbol_opr(Sym, Opr), !,    % get operator
  to_internal(F1, I1),        % recurse on subformulas
  to_internal(F2, I2),
  Int =.. [Opr, I1, I2].      % recompose formula
to_internal(Fml, Int) :-
  Fml =.. [Sym, F],           % similarly for unary formula
  symbol_opr(Sym, Opr), !,
  to_internal(F, I),
  Int =.. [Opr, I].
to_internal(F, F).

%
%  to_external_list(IntList, ExtList)
%  to_internal_list(ExtList, IntList)
%    apply to_external/to_internal to lists
%
to_external_list([], []).
to_external_list([H|T], [HI|TI]) :-
  to_external(H, HI),
  to_external_list(T, TI).

to_internal_list([], []).
to_internal_list([H|T], [HI|TI]) :-
  to_internal(H, HI),
  to_internal_list(T, TI).

%
%  transform(L1, L2)
%    L1 is a list of deductions.
%    L2 has all formulas transformed to internal format.
%
transform([],[]).
transform([deduce(L, F) | Tail], [deduce(LI, FI) | ITail]) :-
  to_internal(F, FI),
  to_internal_list(L, LI),
  transform(Tail, ITail).

%
%  get_atoms(Fml, Atoms) returns a sorted list of the Atoms in Fml
%
get_atoms(Fml, Atoms) :-
  get_atoms1(Fml, UnSorted),
  sort(UnSorted, Atoms).

%
%  get_atoms1(Fml, Atoms)
%    decompose the formula to get the atoms
%
get_atoms1(Fml, Atom) :-
  Fml =.. [_, A, B], !,
  get_atoms1(A, Atom1),
  get_atoms1(B, Atom2),
  union(Atom1, Atom2, Atom).
get_atoms1(Fml, Atom) :-
  Fml =.. [_, A], !,
  get_atoms1(A, Atom).
get_atoms1(A, [A]).

%
%  generate(Atoms, V)
%    for each atom A in the list Atoms,
%    generate a pair, first (A,t) and upon backtracking (A,f)
%
generate([A | ATail], [(A,t) | VTail]) :-
  generate(ATail, VTail).
generate([A | ATail], [(A,f) | VTail]) :-
  generate(ATail, VTail).
generate([], []).

%
%  instance(A, A1, X, C)
%    A1 is an instance of A obtained by substituting C for X.
%    If C is an atom, create instance with C.
%    If C is a variable, check instance and return C.
%  subst_constant(X, C, Vars, Vars1)
%    Vars is a list of variables. Vars1 is Vars with X replaced by C.
%

instance(all(X1, A), all(X2, A1), Y, C) :-
  var(C), !,
  X1 == X2,
  instance(A, A1, Y, C).
instance(all(X, A), all(X, A1), Y, C) :-
  atom(C), !,
  instance(A, A1, Y, C).
instance(ex(X1, A),  ex(X2, A1), Y, C)  :-
  var(C), !,
  X1 == X2,
  instance(A, A1, Y, C).
instance(ex(X, A),  ex(X, A1), Y, C)  :-
  atom(C), !,
  instance(A, A1, Y, C).
instance(A, A1, X, C) :-
  A =..  [Opr, F1, F2],
  symbol_opr(_, Opr), !,
  A1 =.. [Opr, F1I, F2I],
  instance(F1, F1I, X, C),
  instance(F2, F2I, X, C).
instance(neg A, neg A1, X, C) :- !,
  instance(A, A1, X, C).
instance(A, A1, X, C) :-
  A =..  [F | Vars],
  nonvar(A1),
  A1 =.. [F | Vars1],
  subst_constant(X, C, Vars, Vars1).
instance(A, A1, X, C) :-
  A =..  [F | Vars],
  var(A1),
  subst_constant(X, C, Vars, Vars1),
  A1 =.. [F | Vars1].

subst_constant(X1, C, [X2 | Tail], [C | Tail1]) :-
  X1 == X2, !,
  subst_constant(X1, C, Tail, Tail1).
subst_constant(X, C, [Y1 | Tail], [Y2 | Tail1]) :-
  var(C), Y1 == Y2, !,
  subst_constant(X, C, Tail, Tail1).
subst_constant(X, C, [Y | Tail], [Y | Tail1]) :-
  atom(C), !, subst_constant(X, C, Tail, Tail1).
subst_constant(_, _, [], []).

%
%  Systematic construction of semantic tableaux for
%     the predicate calculus.
%

%
%  create(Fml, Tab) - Tab is the tabelau for the formula Fml.
%
%  t(Fmls, Left, Right)
%     Fmls is a list of formula at the root of this tableau and
%     Left and Right are the subtrees (Right ignored for alpha rule).
%     The tableau is constructed by instantiating the logical
%     variables for the subtrees.
%
create_tableau(Fml, Tab) :-
  Tab = t([Fml], _, _, []), 
  extend_tableau(Tab).

%
%  extend_tableau(t(Fmls, Left, Right) - Perform one tableau rule.
%    1. Check for a pair of contradicatory formulas in Fmls (closed).
%    2. Check if Fmls contains only literals (open).
%    3. Perform an alpha or beta rule.
%
extend_tableau(t(Fmls, closed, empty, _)) :- 
  check_closed(Fmls), !.
extend_tableau(t(Fmls, open,   empty, _)) :- 
  contains_only_literals(Fmls), !.
extend_tableau(t(Fmls, Left,   empty, C)) :-
  alpha_rule(Fmls, Fmls1), !,
  Left = t(Fmls1, _, _, C),
  extend_tableau(Left).
extend_tableau(t(Fmls, Left,   Right, C)) :-
  beta_rule(Fmls, Fmls1, Fmls2),
  Left  = t(Fmls1, _, _, C),
  Right = t(Fmls2, _, _, C),
  extend_tableau(Left),
  extend_tableau(Right).
extend_tableau(t(Fmls, Left,   empty, C)) :-
  delta_rule(Fmls, Fmls1, Const), !,
  Left = t(Fmls1, _, _, [Const|C]),
  extend_tableau(Left).
extend_tableau(t(Fmls, Left,   empty, C)) :-
  gamma_rule(Fmls, Fmls1, C), !,
  Left = t(Fmls1, _, _, C),
  extend_tableau(Left).

%  check_closed(Fmls)
%    Fmls is closed if it contains contradictory formulas.
%  contains_only_literals(Fmls)
%    Traverse Fmls list checking that each is a literal.
%  literal(Fml)
%    Fml is a propositional letter or a negation of one.
%
check_closed(Fmls) :-
  member(F1, Fmls), member(neg F2, Fmls), F1 == F2.

contains_only_literals([]).
contains_only_literals([Fml | Tail]) :-
  literal(Fml),
  contains_only_literals(Tail).

literal(Fml)  :- atomic_formula(Fml).
literal(neg Fml) :- atomic_formula(Fml).

atomic_formula(all(_, _)) :- !, fail.
atomic_formula(ex(_, _)) :- !, fail.
atomic_formula(A) :-
  A =..  [Opr, _, _],
  symbol_opr(_, Opr), !, fail.
atomic_formula(neg _) :- !, fail.
atomic_formula(_).

%  alpha_rule(Fmls, Fmls1)
%    Fmls1 is Fmls with an alpha deleted and alpha1, alpha2 added.
%  beta_rule(Fmls, Fmls1, Fmls2)
%    Fmls1 (Fmls2) is Fmls with a beta deleted and beta1 (beta2) added.
%  alpha(A1 opr A2, A1, A2)
%  beta(A1 opr A2, A1, A2)
%    Database of rules for each operator.

alpha_rule(Fmls, [A1, A2 | Fmls1]) :-
  member(A, Fmls),
  alpha(A, A1, A2), !,
  delete(Fmls, A, Fmls1).
alpha_rule(Fmls, [A1 | Fmls1]) :-
  member(A, Fmls),
  A = neg neg A1,
  delete(Fmls, A, Fmls1).
  
alpha(A1 con A2, A1, A2).
alpha(neg (A1 imp A2), A1, neg A2).
alpha(neg (A1 dis A2), neg A1, neg A2).
alpha(A1 eqv A2, A1 imp A2, A2 imp A1).
  
beta_rule(Fmls, [B1 | Fmls1], [B2 | Fmls1]) :-
  member(B, Fmls),
  beta(B, B1, B2),
  delete(Fmls, B, Fmls1).

beta(B1 dis B2, B1, B2).
beta(B1 imp B2, neg B1, B2).
beta(neg (B1 con B2), neg B1, neg B2).
beta(neg (B1 eqv B2),  neg (B1 imp B2), neg (B2 imp B1)).

gamma_rule(Fmls, Fmls4, C) :-
  member(A, Fmls),
  gamma(A, _, dummy), !,        % Check if gamma rule
  (C = [] -> C1 =[a] ; C1 = C),
  gamma_all(C1, A, AList),       % Apply gamma for all constants C
  delete(Fmls, A, Fmls1),       % Re-order: gamma(c), Fmls, gamma
  append(Fmls1, [A], Fmls2),    %   so that substitutions are taken
  append(AList, Fmls2, Fmls3),  %   and universal fml is taken last
  list_to_set(Fmls3, Fmls4).    % Remove duplicates introduced by gamma

gamma(all(X, A1), A2, C) :-
  instance(A1, A2, X, C).
gamma(neg ex(X, A1), neg A2, C) :-
  instance(A1, A2, X, C).

gamma_all([C | Rest], A, [A1 | AList]) :-
  gamma(A, A1, C),
  gamma_all(Rest, A, AList).
gamma_all([], _, []).

delta_rule(Fmls, [A2 | Fmls1], C) :-
  member(A, Fmls),
  delta(A, X, A1), !,
  gensym(a, C),
  instance(A1, A2, X, C),
  delete(Fmls, A, Fmls1).

delta(ex(X, A1), X, A1).
delta(neg all(X, A1), X, neg A1).

%

tableau(Fml) :-
  once(to_internal(Fml, FmlE)),
  once(create_tableau(FmlE, Tab)),
  once(write_tableau(Tab)).

%
%  Justify a Hilbert proof.
%

%
%  proof(List)
%  proof(List, Line, SoFar, Gens)
%    Succeeds if the List of formulas is a proof
%      where SoFar is a list of formulas already proven,
%      and Gens is a list of constants to which Generalization
%      has been applied (used for proviso of deduction theorem).
%      The head of List is the Line'th line in the proof.
%      The justification of a proof is printed.
%
proof(List) :- proof(List, 0, [], []).

proof([], _, _, _).
proof([Fml | Tail], Line, SoFar, Gens) :- 
  Line1 is Line + 1,
  Fml = deduce(_, A),
  axiom(A, N), !,
  write_proof_line(Line1, Fml, ['Axiom ', N]),
  proof(Tail, Line1, [Fml | SoFar], Gens).
proof([Fml | Tail], Line, SoFar, Gens) :- 
  Line1 is Line + 1,
  Fml = deduce(Assump, A),
  member(A, Assump), !,
  write_proof_line(Line1, Fml, ['Assumption']),
  proof(Tail, Line1, [Fml | SoFar], Gens).
proof([Fml | Tail], Line, SoFar, Gens) :- 
  Line1 is Line + 1,
  Fml = deduce(Assump, A imp B),
  nth1(L, SoFar, deduce(Previous, B)),
  member(A, Previous),
  proviso(Gens, A), !,
  delete(Previous, A, Assump),
  D is Line1 - L,
  write_proof_line(Line1, Fml, ['Deduction ', D]),
  proof(Tail, Line1, [Fml | SoFar], Gens).
proof([Fml | Tail], Line, SoFar, Gens) :- 
  Line1 is Line + 1,
  Fml = deduce(_, A),
  nth1(L1, SoFar, deduce(_, B imp A)), 
  nth1(L2, SoFar, deduce(_, B)), !,
  MP1 is Line1 - L1,
  MP2 is Line1 - L2,
  write_proof_line(Line1, Fml, ['MP ', MP1, ',', MP2]),
  proof(Tail, Line1, [Fml | SoFar], Gens).
proof([Fml | Tail], Line, SoFar, Gens) :- 
  Line1 is Line + 1,
  Fml = deduce(_, all(X, A)),
  nth1(L, SoFar, deduce(_, A1)),
  instance(A, A1, X, C), !,
  G is Line1 - L,
  write_proof_line(Line1, Fml, ['Gen ', G]),
  proof(Tail, Line1, [Fml | SoFar], [C | Gens]).
proof([Fml | _], Line, _, _) :-
  Line1 is Line + 1,
  write_proof_line(Line1, Fml, ['Cannot prove']).

%  axiom(A, N)
%    A is the N'th axiom.
%
axiom(A imp (_ imp A), 1).
axiom((A imp (B imp C)) imp ( (A imp B) imp (A imp C)), 2).
axiom(((neg B) imp (neg A)) imp (A imp B), 3).
axiom(all(X, A1) imp A2, 4) :- instance(A1, A2, X, _).
axiom(all(X, A imp B) imp (A imp all(X, B)), 5) :- \+ free_in(A, X).

%
%   proviso(Gens, A)
%     Deduction theorem can only be applied if the constants 
%     to which generalization has been applied (Gen) do
%     occur in the formula A.
%     free_in can be used since a constant is necessarily 'free'.
%
proviso([], _).
proviso([C | Rest], A) :- \+ free_in(A, C), proviso(Rest, A).

%  free_in(A, X)
%    X occurs free in A.
%
free_in(all(X, A), Y) :- \+ X==Y, free_in(A, Y).
free_in(ex(X, A),  Y) :- \+ X==Y, free_in(A, Y).
free_in(A dis B, X)     :- free_in(A, X); free_in(B, X).
free_in(A con B, X)     :- free_in(A, X); free_in(B, X).
free_in(A imp B, X)    :- free_in(A, X); free_in(B, X).
free_in(A eqv B, X)   :- free_in(A, X); free_in(B, X).
free_in(A dif B,  X)    :- free_in(A, X); free_in(B, X).
free_in(neg A, X)        :- free_in(A, X).
free_in(A, X)         :- A =.. [_ | Vars], member_term(X, Vars).

%

test(List) :-
  transform(List, List1),
  proof(List1), !.

%
%  skolem(A, B)
%  skolem(A, ListA, ListE, B)
%    B is A with existential quantifiers replaced by
%      Skolem functions.
%    ListA of universally quantified variables seen
%      so far.
%    ListE of pairs of existentially quantified
%      variables and the associated Skolem function
%      (X, f(...)).
%
skolem(A, A2) :- 
  cnf(A, A1),
  skolem(A1, [], [], A2).

%  Universal quantifier: add variable to list seen
%    so far.

skolem(all(X, A), ListA, ListE, all(X, B)) :- !,
  skolem(A, [X | ListA], ListE, B).

% Existential quantifier: get new function symbol
%   and create f(...) from function symbol and
%   universally quantified variables.

skolem(ex(X, A), ListA, ListE, B) :- !,
  gensym(f, F),
  Function =.. [F | ListA],    
  skolem(A, ListA, [(X, Function) | ListE], B).

skolem(A1 dis A2, ListA, ListE, B1 dis B2) :- !,
  skolem(A1, ListA, ListE, B1),
  skolem(A2, ListA, ListE, B2).
skolem(A1 con A2, ListA, ListE, B1 con B2) :- !,
  skolem(A1, ListA, ListE, B1),
  skolem(A2, ListA, ListE, B2).
skolem(neg A, ListA, ListE, neg B) :- !,
  skolem(A, ListA, ListE, B).

% Substitute in atoms for existentially
%   quantified variables.

skolem(A, _, ListE, B) :-
  A =.. [F | Vars],
  subst_var(Vars, Vars1, ListE),
  B =.. [F | Vars1].

skolem_to_clausal(all(_,F), F1) :- !,
  skolem_to_clausal(F, F1).
skolem_to_clausal(F, F1) :-
  cnf_to_clausal(F, F1).

%
%  clashing(C1, L1, C2, L2, Subst) -
%    Literals clash if one is the negation of the other and
%      they unify. Return the mgu substitution.
%
clashing(C1, L1, C2, neg L2, Subst) :-
  member(L1, C1),
  member(neg L2, C2),
  unify(L1, L2, Subst),
  !.
clashing(C1, neg L1, C2, L2, Subst) :-
  member(neg L1, C1),
  member(L2, C2),
  unify(L1, L2, Subst),
  !.

%
%  delete_lit(C, L, Substution, Result)
%    In clause C, delete all occurrences of literal L
%      after performing Subsitution, and return Result.
%    Perform substitution and call:
%  delete_lit1(C, L, Result)
%
delete_lit(C, L, Subst, Result) :-
  apply_subst(C, C1, Subst),
  apply_subst([L], [L1], Subst),
  delete_lit1(C1, L1, Result).

delete_lit1([Head|Tail], L, Result) :-
  Head == L, !,
  delete_lit1(Tail, L, Result).
delete_lit1([Head|Tail], L, [Head|Result]) :- !,
  delete_lit1(Tail, L, Result).
delete_lit1([], _, []).

%
%  clause_union(C1, C2, Result)
%    Perform set union of C1, C2,
%      using member_term so as not to instantiate variables.
%
clause_union([Head|Tail], C, Result) :-
  member_term(Head, C), !,
  clause_union(Tail, C, Result).
clause_union([Head|Tail], C, [Head|Result]) :- !,
  clause_union(Tail, C, Result).
clause_union([], C, C).

%
%  apply_subst(List, NewList, Substitution)
%    Apply Substitution to all elements of List to give NewList.
%
apply_subst([], [], _).
apply_subst([Head|Tail], [Head1|Tail1], Subst) :-
  subst_for_var(Head, Head1, Subst),
  apply_subst(Tail, Tail1, Subst).

%
%  subst_for_var(Term, NewTerm, Substitution)
%    Apply Substitution for all variables in Term to give NewTerm.
%    If compound term, decompose and call apply_subst.
%
subst_for_var(Term, Term1, Subst) :-
  nonvar(Term),
  Term  =.. [F|Args], !,
  apply_subst(Args, Args1, Subst),
  Term1 =.. [F|Args1].
subst_for_var(V, V2, [V1 eq V2 | _]) :-
  V == V1, !.
subst_for_var(V, V2, [_ | Tail]) :-
  subst_for_var(V, V2, Tail).
subst_for_var(V, V, []).

%
%  unify(A, B, Substitution)
%    Returns an mgu in Substitution if A can be unified.
%    If not: returns [failure3,Fml], or [failure4,Fml]
%      if A and B cannot be unified due to failure in rule 3 or 4.
%
unify(A1, A2, Subst) :-
  A1 =.. [Pred | Args1],
  A2 =.. [Pred | Args2],
  create_equations(Args1, Args2, Eq),
  solve(Eq, Subst).

%
%  create_equations(Arg1, Arg2, Eq)
%    Creates a list of equations from argument lists Arg1, Arg2.
%
create_equations([Head1 | Tail1],
              [Head2 | Tail2], 
              [Head1 eq Head2 | List]) :- !,
  create_equations(Tail1, Tail2, List).
create_equations([], [], []).

%
%  solve(Eq, Substitution)
%    As in unify, but A and B are now a list of equations Eq.
%  solve(Front, Back, Status, Substitution)
%    The list of equations is maintained as two partial
%      lists Front, Back, where the Current equation is the
%      head of the list Back.
%    Status is used to stop the algorithm when:
%      the initial status notmodified has not been changed
%        after traversing the entire list, or,
%      failure3 or failure4 is set.
%
solve(Eq, Subst) :-
  solve([], Eq, notmodified, Subst).

% Stop algorithm upon failure, return equation which caused it.

solve(_, [Current|_], failure3, [failure3, Current]) :- !.
solve([Current], _,   failure4, [failure4, Current]) :- !.

% Try rules 1-4 on Current.
%   (1) Current is modified and put back on list.
%   (2) Current is deleted.
%   (3) Current is deleted and new equations appended to front of Back.
%   (4) Substitute Current in both Front and Back; let Current be Front.
%
solve(Front, [Current | Back], Status, Result) :-
  rule1(Current, Current1), !,
  solve(Front, [Current1 | Back], Status, Result).
solve(Front, [Current | Back], Status, Result) :-
  rule2(Current), !,
  solve(Front, Back, Status, Result).
solve(Front, [Current | Back], _, Result) :-
  rule3(Current, NewList, Status), !,
  append(NewList, Back, NewBack),
  solve(Front, NewBack, Status, Result).
solve(Front, [Current | Back], _, Result) :-
  append(Front, Back, List),
  rule4(Current, List, NewList, Status), !,
  solve([Current], NewList, Status, Result).
     
%  No rule applies:
%    continue with next equation,
%    if none, restart from beginning of list if modified,
%    otherwise, terminate.
%
solve(Front, [Current | Rest], Mod, Result) :- !,
  append(Front, [Current], NewFront),
  solve(NewFront, Rest, Mod, Result).
solve(List, [], modified, Result) :- !,
  solve([], List, notmodified, Result).
solve(Result, [], _, Result).

rule1(T eq X, X eq T) :- nonvar(T), var(X).   % Exchange sides of equation.

rule2(X eq Y)         :- X == Y.              % Same variable X eq X.

rule3(T1 eq T2, List, notmodified) :-            % Unpack f(...) eq f(...)
  nonvar(T1),
  nonvar(T2),
  T1 =.. [F | Subterms1],
  T2 =.. [F | Subterms2],
  create_equations(Subterms1, Subterms2, List).
rule3(T1 eq T2, [T1 eq T2], failure3) :-      % Fail if functors different.
  nonvar(T1),
  nonvar(T2),
  functor(T1, F1, _),
  functor(T2, F2, _),
  F1 \== F2.

rule4(X eq T, List, List, failure4) :-    % Fails if occurs check succeeds.
  var(X),
  occur(X, T), !.                           
rule4(X eq T, List, NewList, notmodified) :-
  var(X),
  subst_list(X, T, List, NewList),
  List \== NewList.

%
%  occur(X, T) - X occurs in the term T.
%  occur_list(X, List) -
%    Apply occur(X) to all elements of the list,
%      succeed if the sublist of elements on which it succeeds is non-empty.
%
occur(X, T) :- X == T, !.       % T is X
occur(X, T) :-                  % Recurse on subterms
  nonvar(T),
  T =.. [_ | Subterms],
  occur_list(X, Subterms).

occur_list(X, List) :-
  sublist(occur(X), List, [_|_]).

%
%  subst_list(X, T, List, NewList)
%    Substitute T for X in all elements of List, result is NewList.
%  subst(X, T, Term, NewTerm)
%    Substitute T for X in Term, result is NewTerm.
%
subst_list(X, T, List, NewList) :-
  maplist(subst(X, T), List, NewList).

subst(X, T, Term, T) :- X == Term, !.   % If Term is X, return T.
subst(X, T, Term, NewTerm) :-           % Recurse on subterms.
  nonvar(Term),
  Term =.. [F | SubTerms], !,
  subst_list(X, T, SubTerms, NewSubTerms),
  NewTerm =.. [F | NewSubTerms].
subst(_, _, Term, Term).                % Otherwise, do nothing.

resolution(XFml) :-
  NegFml = ~XFml,
  write(NegFml), nl,
  to_internal(NegFml,Fml),
  skolem(Fml,Cnf),
  to_external(Cnf,XCnf),
  write(XCnf), nl,
  skolem_to_clausal(Cnf,Cls),
  write(Cls), nl,
  resolve(Cls).

qed(A) :-
  nl,
  write_formula(A), nl,
  to_internal(~A, AE),
  skolem(AE, B),
  to_external(B, BE),
  nl,
  write_formula(BE), nl,
  skolem_to_clausal(B, S),
  nl,
  write_clauses(S), nl,
  resolve(S), !.