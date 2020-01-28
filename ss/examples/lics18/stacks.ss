#options --work=send --syntax=implicit

type stack = &{push : &{b0 : stack, b1 : stack},
               pop : <|<|+{none : 1, some : +{b0 : stack, b1 : stack}}}


proc elem0 : stack |- stack
proc elem1 : stack |- stack
proc empty :     . |- stack

proc elem0 = caseR ( push => caseR ( b0 => elem0 || elem0
                                   | b1 => elem0 || elem1 )
                   | pop => R.some ; R.b0 ; <-> )

proc elem1 = caseR ( push => caseR ( b0 => elem1 || elem0
                                   | b1 => elem1 || elem1 )
                   | pop => R.some ; R.b1 ; <-> )

proc empty = caseR ( push => caseR ( b0 => empty || elem0
                                   | b1 => empty || elem1 )
                   | pop => R.none ; closeR )

exec empty