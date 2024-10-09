w(5,2186369,a,det).
w(2107,4249,abandon,v).
w(5204,1110,abbey,n).
w(966,10468,ability,n).
w(321,30454,able,a).
w(6277,809,abnormal,a).
w(3862,1744,abolish,v).
w(5085,1154,abolition,n).
w(4341,1471,abortion,n).
w(179,52561,about,adv).
w(69,144554,about,prep).
w(3341,2139,above,a).
w(942,10719,above,adv).
w(786,12889,above,prep).
w(2236,3941,abroad,adv).
w(5106,1146,abruptly,adv).

% Question 1.1
ambiguous(Word) :- 
    w(_, _, Word, C1), % Take word and its class1
    w(_, _, Word, C2), % Take same word with its class2
    C1 \= C2, % If classes are different
    !. % end

% Question 1.2

display(N) :-
    w(SortOrder, _, Word, WordClass), % Extract all except frequency
    SortOrder =< N, % Check
    write(Word), write(' '), write(WordClass), nl,
    fail.  % Fail backtrack and find more solutions

% Question 3.1

firstlast([X, X]). %Base case
firstlast([X,_|T]) :- % Split list up
    firstlast([X|T]). %Recursion

% Question 3.2

firstlasta(List) :-
    append([X|_], [X],List).

% Question 4
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

% Question 4.1

test(Score) :- 
    score(test, _, Score). %Get the score from test
test(Score) :- 
    score(exam, _, Score). %Get the score from exam

% Question 4.2

problem :-
    score(test, Student, TestScore), %Getting student name and test score
    score(exam, Student, ExamScore), %Getting student name and exam score
    TestScore > 2 * ExamScore, % CHeck if the test score is more than twice as big as exam score
    write(Student), write('\n'), %print out the results
    fail.
problem.


% Question 5

/*
theory Assignment2 imports Logic
begin

section ‹Question 5›

proposition ‹[] ⪢ ((p → q) → p) → p # []›
proof -
  from Imp_R have ?thesis if ‹
    p # []
    ⪢
    ((p → q) → p) # []
    ›
    using that by force
  with Imp_R have ?thesis if ‹
    (p → q) #
    p # []
    ⪢
    p # []
    ›
    using that by force
  with Imp_L have ?thesis if ‹
    ((p → q) → p) #
    (p → q) #
    p # []
    ⪢
    p # []
    ›
    using that by force
  with Basic show ?thesis
    by force
qed

end
*/

