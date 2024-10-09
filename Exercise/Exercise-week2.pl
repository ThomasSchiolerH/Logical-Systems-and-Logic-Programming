% "swipl 'path' " to start


% Special Exercise
% list(List) :- length(List,_) .

% Exercise 1
% Write a program interval_member(?Integer,+List,+IntegerMin,+IntegerMax) 
% that succeeds if and only if Integer is a member of List and strictly between IntegerMin and IntegerMax.

% interval_member(Int,List,IntMin,IntMax) :- member(Int,List), IntMin<Int, Int<IntMax .

% Exercise 2
% Write a program list(?List) that succeeds if and only if List is a list.

/*list(List) :- 
    List = [] .

list([_|Rest]) :- 
    list(Rest) .*/

% Exercise 3
% Write a program select(?Elem,?List1,?List2) that succeeds 
% if and only if List2 is List1 with Elem 
% removed (it removes one occurrence of Elem in List1 to give List2 and 
% the elements are selected in the order of appearance in the list).

select(Elem, [Elem|Tail], Tail) .
select(Elem, [Head|Tail1], [Head|Tail2]) :-
    select(Elem, Tail1, Tail2) .

