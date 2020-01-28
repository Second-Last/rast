#options --terminate=equi

type resp = +{ none : 1,
               some : +{ b0 : store, b1 : store } }

type store = &{ ins : &{ b0 : store, b1 : store },
                del : resp }

proc triv : store
proc triv = caseR ( ins => caseR ( b0 => triv | b1 => triv)
                  | del => R.some ; R.b0 ; triv )

proc consume : store |- 1
proc consume = L.del ; caseL ( none => waitL ; closeR
                             | some => caseL ( b0 => consume
                                             | b1 => consume ))
