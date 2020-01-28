#options --work=send --syntax=explicit
#test error

type bits = +{b0 : bits, b1 : bits, $ : 1}

type queue{n} = &{enq : &{b0 : <{2*n}| queue{n+1}, b1 : <{2*n}| queue{n+1}},
                  deq : <{2}| +{none : ?{n = 0}. 1,
                                some : ?{n > 0}. +{b0 : queue{n-1}, b1 : queue{n-1}}}}

proc bit0{n} : queue{n} |- queue{n+1}
proc bit1{n} : queue{n} |- queue{n+1}
proc empty : . |- queue{0}

proc bit0{n} = caseR ( enq => caseR ( b0 => getR{2*(n+1)} ; L.enq ; L.b0 ; payL{2*n} ; bit0{n+1}
                                    | b1 => getR{2*(n+1)} ; L.enq ; L.b1 ; payL{2*n} ; bit0{n+1} )
                     | deq => getR{2} ; R.some ; assertR {n > 0} ; R.b0 ; <-> )
proc bit1{n} = caseR ( enq => caseR ( b0 => getR{2*(n+1)} ; L.enq ; L.b0 ; payL{2*n} ; bit1{n+1}
                                    | b1 => getR{2*(n+1)} ; L.enq ; L.b1 ; payL{2*n} ; bit1{n+1} )
                     | deq => getR{2} ; R.some ; assertR {n > 0} ; R.b1 ; <-> )
proc empty   = caseR ( enq => caseR ( b0 => getR{0} ; empty || bit0{0}
                                    | b1 => getR{0} ; empty || bit1{0} )
                     | deq => getR{2} ; R.none ; assertR {0 = 0} ; closeR )

proc ex11 : . |{(0+2+4+6)+8}- queue{4}
proc ex11 = empty || L.enq ; L.b1 ; payL{0} ; L.enq ; L.b0 ; payL{2} ; L.enq ; L.b1 ; payL{4} ; L.enq ; L.b1 ; payL{6} ; <->

(*
exec ex11
*)

proc pop{n} : queue{n+1} |{3}- queue{n}
proc pop{n} = L.deq ; payL{2} ;
              caseL ( none => impossibleL {n+1 = 0}
                    | some => assumeL {n+1 > 0} ;
                      caseL ( b0 => <-> | b1 => <-> ) )

proc ex12 : . |{(0+2+2+3)+6}- queue{2}
proc ex12 = empty || L.enq ; L.b1 ; payL{0} ; L.enq ; L.b0 ; payL{2} ; pop{1} || L.enq ; L.b1 ; payL{2} ; <->
