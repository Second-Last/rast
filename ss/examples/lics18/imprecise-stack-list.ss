#options --work=send --syntax=implicit
#test success

type blist = +{cons : |>|> +{zero : blist, one : blist}, nil : |>|> 1}

type stack = &{ins : <|<|<|<| &{zero : stack, one : stack},
               del : +{none : 1, some : +{zero : stack, one : stack}}}

proc nil : . |{4}- blist
proc cons0 : blist |{4}- blist
proc cons1 : blist |{4}- blist

proc nil = R.nil ; closeR

proc cons0 = R.cons ; R.zero ; <->

proc cons1 = R.cons ; R.one ; <->

proc stack_new : . |{8}- stack
proc stacks : blist |{4}- stack

proc stack_new = nil || stacks

proc stacks = caseR ( ins => caseR ( zero => cons0 || stacks
                                   | one  => cons1 || stacks )
                    | del => caseL ( cons => caseL ( zero => R.some ; R.zero ; stacks
                                                   | one  => R.some ; R.one ; stacks )
                                   | nil  => waitL ; R.none ; closeR ) )