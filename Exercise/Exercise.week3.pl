% "swipl 'path' " to start

% Exercise 1

membera(X,List) :-
    append(_,[X|_], List).

% In this definition, we use append to split the List into two parts: the first part is represented by _,
% (an anonymous variable, indicating that we don't care about its content), and the second part is represented 
% by [X|_], where X is the element we are checking for membership, and _ again represents the rest of the list. 
% If the append can successfully split the list this way, it means that X is a member of the List.

% Exercise 2
% See logic.pl

% Exercise 3

% Exercise 4 & 5
% Remember to negate them first and see if it closes in order to see if it is proven.

% Exercise 6
