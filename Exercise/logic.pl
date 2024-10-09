% logic.pl

%
% Propositional logic
%

%
% Logical operators
%

%
% Symbolic operators for external use
%
:- op(650,xfy,\<=>). /* difference  */
:- op(650,xfy,<=>).  /* equivalence */ 
:- op(640,xfy,=>).   /* implication */ 
:- op(630,xfy,\).    /* disjunction */ 
:- op(620,xfy,&).    /* conjunction */ 
:- op(610,fy, ~).    /* negation    */ 

%
% Alphabetic operators for internal use
%
:- op(650,xfy,dif).  /* difference  */
:- op(650,xfy,eqv).  /* equivalence */ 
:- op(640,xfy,imp).  /* implication */ 
:- op(630,xfy,dis).  /* disjunction */ 
:- op(620,xfy,con).  /* conjunction */ 
:- op(610,fy, neg).  /* negation    */

%
% Translation between operator symbols
%
symbol_opr(\<=>,dif).
symbol_opr(<=>, eqv).
symbol_opr(=>,  imp).
symbol_opr(\,   dis).
symbol_opr(&,   con).
symbol_opr(~,   neg).

%
% tt(Fml,V,TV)
%   under the evaluation V the formula Fml has the truth value TV
%
tt(A eqv B,V,TV) :- tt(A,V,TVA), tt(B,V,TVB), opr(eqv,TVA,TVB,TV).
tt(A dif B,V,TV) :- tt(A,V,TVA), tt(B,V,TVB), opr(dif,TVA,TVB,TV).
tt(A imp B,V,TV) :- tt(A,V,TVA), tt(B,V,TVB), opr(imp,TVA,TVB,TV).
tt(A dis B,V,TV) :- tt(A,V,TVA), tt(B,V,TVB), opr(dis,TVA,TVB,TV).
tt(A con B,V,TV) :- tt(A,V,TVA), tt(B,V,TVB), opr(con,TVA,TVB,TV).
tt(neg A,  V,TV) :- tt(A,V,TVA), negate(TVA,TV).
tt(A,      V,TV) :- member((A,TV),V).

%
% Semantic definitions of propositional operators
%   opr for binary operators, negate for negation
%
opr(dis,t,t,t). opr(dis,t,f,t). opr(dis,f,t,t). opr(dis,f,f,f).
opr(con,t,t,t). opr(con,t,f,f). opr(con,f,t,f). opr(con,f,f,f).
opr(dif,t,t,f). opr(dif,t,f,t). opr(dif,f,t,t). opr(dif,f,f,f).
opr(eqv,t,t,t). opr(eqv,t,f,f). opr(eqv,f,t,f). opr(eqv,f,f,t).
opr(imp,t,t,t). opr(imp,t,f,f). opr(imp,f,t,t). opr(imp,f,f,t).

negate(t,f).
negate(f,t).

%
% IO
%

%
% term_length(T,L) - L is the length of term T
%
term_length(T,L) :-
  term_to_atom(T,A),
  string_to_atom(S,A),
  string_length(S,L).

%
% write_tt_title(Fml,Atoms)
%   write the truth table title: formula and atoms
%
write_tt_title(Fml,Atoms) :-
  to_external(Fml,EFml),
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
% write_tt_line(Fml,V,TV)
%   write a truth table line,
%   Fml is a formula (used for indenting)
%   V a valuation and TV the truth value
%
write_tt_line(Fml,V,TV) :-
  to_external(Fml,EFml),
  term_length(EFml,L),
  tab(L),
  write('  '),
  write_valuation(V),
  write('   '),
  write(TV),
  nl.

%
% write_valuation(List)
%   write the valuations in the List with blank separators
%
write_valuation([]).                                                                       
write_valuation([(_,TV)|Tail]) :-
  write(TV),
  write(' '),
  write_valuation(Tail).

%
% Translates internal to external symbols and conversely
%

%
% to_external(Int,Ext)
%   translates Int in internal format to Ext in external format.
%
to_external(Fml,Ext) :-
  Fml =.. [Opr,F1,F2], !,
  symbol_opr(Sym,Opr),
  to_external(F1,E1),
  to_external(F2,E2),
  Ext =.. [Sym,E1,E2].
to_external(Fml,Ext) :-
  Fml =.. [Opr,F], !,
  symbol_opr(Sym,Opr),
  to_external(F,E),
  Ext =.. [Sym,E].
to_external(F,F).

%
% to_internal(Ext,Int)
%   translates Ext in external format to Int in internal format.
%
to_internal(Fml,Int) :-
  Fml =.. [Sym,F1,F2], !,
  symbol_opr(Sym,Opr),
  to_internal(F1,I1),
  to_internal(F2,I2),
  Int =.. [Opr,I1,I2].
to_internal(Fml,Int) :-
  Fml =.. [Sym,F], !,
  symbol_opr(Sym,Opr),
  to_internal(F,I),
  Int =.. [Opr,I].
to_internal(F,F).

%
% Handling atoms
%

%
% get_atoms(Fml,Atoms) returns a sorted list of the Atoms in Fml
%
get_atoms(Fml,Atoms) :-
  get_atoms1(Fml,UnSorted),
  sort(UnSorted,Atoms).

%
% get_atoms1(Fml,Atoms) decompose the formula to get the atoms
%
get_atoms1(Fml,Atom) :-
  Fml =.. [_,A,B], !,
  get_atoms1(A,Atom1),
  get_atoms1(B,Atom2),
  union(Atom1,Atom2,Atom).
get_atoms1(Fml,Atom) :-
  Fml =.. [_,A], !,
  get_atoms1(A,Atom).
get_atoms1(A,[A]).

%
% generate(Atoms,V)
%   for each atom A in the list Atoms,
%   generate a pair, first (A,t) and upon backtracking (A,f)
%
generate([A|ATail],[(A,t)|VTail]) :-
  generate(ATail,VTail).
generate([A|ATail],[(A,f)|VTail]) :-
  generate(ATail,VTail).
generate([],[]).

%
% Print a truth table
%
% truthtable(+XFml) prints the truth table for the formula XFml
%
% to_internal converts a formula to the internal format
% get_atoms gets a list Atoms of the atoms in Fml
% write_tt_title prints a title line
% generate creates a valuation for the Atoms
%   a valuation is a list of pairs (A,TV),where
%     A is a propositional symbol and
%     TV is the value assigned to it
% tt computes the truth value of a formula under a valuation
% write_tt_line prints a line of the truth table
%    
% failure is used to backtrack so that generate can create another valuation
%

truthtable(XFml) :-
  to_internal(XFml,Fml),
  get_atoms(Fml,Atoms),
  write_tt_title(Fml,Atoms),
  generate(Atoms,V),
  tt(Fml,V,TV),
  write_tt_line(Fml,V,TV),
  fail.
truthtable(_).