#options --work=send --syntax=implicit
#test success

type queue{n} = &{enq : <{2*n}| &{b0 : queue{n+1}, b1 : queue{n+1}},
                  deq : <{2}| +{none : !{n=0} 1,
                                some : !{n>0} +{b0 : queue{n-1}, b1 : queue{n-1}}}}

proc bit0{n} : queue{n} |- queue{n+1}
proc bit1{n} : queue{n} |- queue{n+1}
proc empty : . |- queue{0}

proc bit0{n} = caseR ( enq => caseR ( b0 => L.enq ; L.b0 ; bit0{n+1}
                                    | b1 => L.enq ; L.b1 ; bit0{n+1} )
                     | deq => R.some ; assertR {n+1>0} ; R.b0 ; <-> )
proc bit1{n} = caseR ( enq => caseR ( b0 => L.enq ; L.b0 ; bit1{n+1}
                                    | b1 => L.enq ; L.b1 ; bit1{n+1} )
                     | deq => R.some ; assertR {n+1>0} ; R.b1 ; <-> )
proc empty = caseR ( enq => caseR ( b0 => empty || bit0{0}
                                  | b1 => empty || bit1{0} )
                   | deq => R.none ; assertR {0=0} ; closeR )

proc dealloc{n} : queue{n} |{2*n+2+2}- 1
proc dealloc{n} = L.deq ;
                  caseL ( none => assumeL {n = 0} ; waitL ; closeR
                        | some => assumeL {n > 0} ; caseL ( b0 => dealloc{n-1} | b1 => dealloc{n-1}) )

proc waitq : queue{0} |{4}- 1
proc waitq = L.deq ;
             caseL ( none => assumeL {0 = 0} ; waitL ; closeR
                   | some => impossibleL {0 > 0}) % continuation unreachable; this branch is impossible

proc ex11 : . |{0+2+4+6}- queue{4}
proc ex11 = empty || L.enq ; L.b1 ; L.enq ; L.b0 ; L.enq ; L.b1 ; L.enq ; L.b1 ; <->
exec ex11

proc ex11dealloc : . |{0+2+4+6+(2*4+2+2)}- 1
proc ex11dealloc = ex11 || dealloc
exec ex11dealloc
