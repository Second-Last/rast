#options --terminate=equi

type store = &{ ins : &{ b0 : store, b1 : store },
                del : +{ none : 1, some : +{ b0 : store, b1 : store } } }

                         

proc triv : store
proc triv = caseR ( ins => caseR ( b0 => triv | b1 => triv)
                  | del => R.some ; R.b0 ; triv )
