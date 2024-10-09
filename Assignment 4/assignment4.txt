:- ensure_loaded(database).


% Q1.1
score(test,xenia,50).
score(test,alice,99).
score(test,bruce,22).
score(test,carol,77).
score(test,dorit,50).
score(test,erica,22).
score(exam,peter,42).
score(exam,alice,11).
score(exam,bruce,88).
score(exam,carol,33).
score(exam,dorit,50).
score(exam,erica,66).
score(exam,james,77).

students(List) :- 
    findall(Name, score(_, Name, _), Names), % Find all names 
    sort(Names,List), % Sort the names from the list
    !. % So it does not back track

% Q1.2
money(M) :-
    findall(Score, (score(exam, _, Score), Score>40), Scores), % Find all Score where the Score is >40
    length(Scores,Students), % Length of Scores gives the number of students with >40
    M is Students*1000, % Multiply number of students with 1000
    !.

% Q3.1
member1([Head|Tail]) :- %Split the list in h and t
    member(Head, Tail), % Check if H is in T
    !. % No backtrack

% Q3.2
p([], []) :- !. %base case
p([Head|Tail], Sorted) :- % a non empty list
    p(Head, HList),
    p(Tail, TList),
    append(HList, TList, ComboList),
    sort(ComboList, Sorted),
    !.
p(Element, [Element]). %catch the rest

% Q4.1
selectlist(List) :-
    findall(Word, (w(SortOrder, _, Word, WordClass), SortOrder =< 100, (WordClass = n; WordClass = v)), Words),
    sort(Words, List).

% Q4.2
dump :-
    w(_,_,Word,a),
    w(_,_,Word,adv),
    w(_,_,Word,WordClass),
    WordClass \= a, 
    WordClass \= adv,
    write(Word), write(' '), write(WordClass).