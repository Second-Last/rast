% PDA checking for matching left/right parentheses
% input of type 'word' on the left
% stack of type 'stack' on the right
% final answer (true/false) given on the right

% This version checks timing

#options --time=recv --syntax=implicit
#test success

type bool = +{true : `1, false : `1}

% 'left' and '$' are processed instantaneously
% 'right' requires one tick pause so 'left' can be
% popped from the stack.
type word = +{left : `word, right : `()word, $ : `1}
type stack = &{left : `<>stack, $ : `<>bool}

proc match   :    word |- <>stack   % match left/right parens
proc push    : <>stack |- <>stack   % push 'left' onto stack
proc pop     :  ()word |- <>stack   % pop stack
proc empty   : <>stack |- <>bool    % empty stack
proc rejectR :       . |- <>stack   % consume stack and reject
proc rejectL :    word |- <>bool    % consume input and reject

proc match = caseL ( left => match || push
                   | right => pop
                   | $ => waitL ; caseR ( left => rejectR
                                        | $ => R.true ; closeR ) )

proc push = (L.left ; <->)
proc pop = caseR ( left => match
                 | $ => rejectL )
proc empty = (L.$ ; <->)

proc rejectL = caseL ( left => rejectL
                     | right => rejectL
                     | $ => R.false ; waitL ; closeR )
proc rejectR = caseR ( left => rejectR
                     | $ => R.false ; closeR )

% accept "(()())"
proc ex1 : <>bool
proc ex1 = (R.left ; R.left ; R.right ; R.left ; R.right ; R.right ; R.$ ; closeR)
           [word] match || empty
exec ex1

% reject "(()))()"
proc ex2 : <>bool
proc ex2 = (R.left ; R.left ; R.right ; R.right ; R.right ; R.left ; R.right ; R.$ ; closeR)
           [word] match || empty
exec ex2

% reject "())"
proc ex3 : <>bool
proc ex3 = (R.left ; R.left ; R.right ; R.$ ; closeR)
           [word] match || empty
exec ex3
