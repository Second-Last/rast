#options --syntax=explicit
#test success

type stack{n} = &{ push : &{ b0 : stack{n+1},
                             b1 : stack{n+1} },
                   pop  : +{ none : ?{n = 0}. 1,
                             some : ?{n > 0}. +{ b0 : stack{n-1},
                                                 b1 : stack{n-1} } } }

proc empty : stack{0}
proc bit0{n} : stack{n} |- stack{n+1}
proc bit1{n} : stack{n} |- stack{n+1}

proc empty = caseR ( push => caseR ( b0 => empty || bit0{0}
                                   | b1 => empty || bit1{0} )
                   | pop => R.none ; assertR {0 = 0} ; closeR )
proc bit0{n} = caseR ( push => caseR ( b0 => bit0{n} || bit0{n+1}
                                     | b1 => bit0{n} || bit1{n+1} )
                     | pop => R.some ; assertR {n+1 > 0} ;
                              R.b0 ; <-> )
proc bit1{n} = caseR ( push => caseR ( b0 => bit1{n} || bit0{n+1}
                                     | b1 => bit1{n} || bit1{n+1} )
                     | pop => R.some ; assertR {n+1 > 0} ;
                              R.b1 ; <-> )

proc dealloc0 : stack{0} |- 1
proc dealloc0 = L.pop ; caseL ( none => assumeL {0 = 0} ; <->
                              | some => impossibleL {0 > 0} )

proc pop1{n} : stack{n+1} |- stack{n}
proc pop1{n} = L.pop ; caseL ( none => impossibleL {n+1 = 0}
                             | some => assumeL {n+1 > 0} ;
                               caseL ( b0 => <-> | b1 => <-> ) )

proc dealloc{n} : stack{n} |- 1
proc dealloc{n} = L.pop ; caseL ( none => assumeL {n = 0} ; <->
                                | some => assumeL {n > 0} ;
                                  caseL ( b0 => dealloc{n-1}
                                        | b1 => dealloc{n-1} ) )

proc push3 : stack{3}
proc push3 = empty || L.push ; L.b0 ; L.push ; L.b1 ; L.push ; L.b0 ; pop1{2} || L.push ; L.b1 ; <->
exec push3

proc ex3 : 1
proc ex3 = push3 || dealloc{3}
exec ex3
