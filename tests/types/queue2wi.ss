#options --work=send --syntax=implicit
#test success

type bits = +{b0 : bits, b1 : bits, $ : 1}

type queue{n} = &{enq : &{b0 : <{2*n}| queue{n+1}, b1 : <{2*n}| queue{n+1}},
                  deq : <{2}| +{none : ?{n = 0}. 1,
                                some : ?{n > 0}. +{b0 : queue{n-1}, b1 : queue{n-1}}}}

proc bit0{n} : queue{n} |- queue{n+1}
proc bit1{n} : queue{n} |- queue{n+1}
proc empty : . |- queue{0}

proc bit0{n} = caseR ( enq => caseR ( b0 => L.enq ; L.b0 ; bit0{n+1}
                                    | b1 => L.enq ; L.b1 ; bit0{n+1} )
                     | deq => R.some ; R.b0 ; <-> )
proc bit1{n} = caseR ( enq => caseR ( b0 => L.enq ; L.b0 ; bit1{n+1}
                                    | b1 => L.enq ; L.b1 ; bit1{n+1} )
                     | deq => R.some ; R.b1 ; <-> )
proc empty   = caseR ( enq => caseR ( b0 => empty || bit0{0}
                                    | b1 => empty || bit1{0} )
                     | deq => R.none ; closeR )

proc ex11 : . |{(0+2+4+6)+8}- queue{4}
proc ex11 = empty || L.enq ; L.b1 ; L.enq ; L.b0 ; L.enq ; L.b1 ; L.enq ; L.b1 ; <->
exec ex11

proc pop{n} : queue{n+1} |{3}- queue{n}
proc pop{n} = L.deq ;
              caseL ( (* insert this branch ----> none => impossibleL {n+1 = 0} *)
                      some => caseL ( b0 => <-> | b1 => <-> ) )

proc ex12 : . |{(0+2+2+3)+6}- queue{2}
proc ex12 = empty || L.enq ; L.b1 ; L.enq ; L.b0 ; pop{1} || L.enq ; L.b1 ; <->
exec ex12
