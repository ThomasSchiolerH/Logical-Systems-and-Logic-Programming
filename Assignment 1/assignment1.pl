% Below please see the solutions for exercises 3.1 and 3.2

% Question 3.1
member2(Elem, [Elem, Elem | _]). % The consecutive element appears in the start of the list
member2(Elem, [_ | Remain]) :-
    member2(Elem, Remain). % The element appears in the remaining part of the list, checked recursively

% Question 3.2
member2a(Elem, List) :-
    append(_, [Elem, Elem | _], List). % The consecutive element appears in a list using the `append` predicate.