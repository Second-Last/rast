#options --work=send --syntax=explicit
#test error

type bits = +{b0 : bits, b1 : bits, $ : 1}

type queue{p} = &{enq : &{b0 : <{p+2}| queue{p+2}, b1 : <{p+2}| queue{p+2}},
                  deq : <{2}| +{none : ?{p = 0}. 1,
                                some : ?{p > 1}. +{b0 : queue{p-2}, b1 : queue{p-2}}}}

proc bit0{p} : queue{p} |- queue{p+2}
proc bit1{p} : queue{p} |- queue{p+2}
proc empty : . |- queue{0}

proc bit0{p} = caseR ( enq => caseR ( b0 => getR{p} ; L.enq ; L.b0 ; payL{p} ; bit0{p+2}
                                    | b1 => getR{p} ; L.enq ; L.b1 ; payL{p} ; bit0{p+2} )
                     | deq => getR{2} ; R.some ; assertR {p+2 > 1} ; R.b0 ; <-> )
proc bit1{p} = caseR ( enq => caseR ( b0 => getR{p} ; L.enq ; L.b0 ; payL{p} ; bit1{p+2}
                                    | b1 => getR{p} ; L.enq ; L.b1 ; payL{p} ; bit1{p+2} )
                     | deq => getR{2} ; R.some ; assertR {p+2 > 1} ; R.b1 ; <-> )
proc empty   = caseR ( enq => caseR ( b0 => getR{2} ; empty || bit0{0}  (* potential mismatch *)
                                    | b1 => getR{2} ; empty || bit1{0} )
                     | deq => getR{2} ; R.none ; assertR {0 = 0} ; closeR )

proc ex11 : . |{(0+2+4+6)+8}- queue{8}
proc ex11 = empty || L.enq ; L.b1 ; payL{0} ; L.enq ; L.b0 ; payL{2} ; L.enq ; L.b1 ; payL{4} ; L.enq ; L.b1 ; payL{6} ; <->

(*
exec ex11
*)