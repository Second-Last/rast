#options --work=send --syntax=explicit
#test error

type bits = +{b0 : bits, b1 : bits, $ : 1}

type queue{p} = &{enq : &{b0 : <{p}| queue{p+2}, b1 : <{p}| queue{p+2}}}

proc bit0{p} : queue{p} |- queue{p+2}
proc bit1{p} : queue{p} |- queue{p+2}
proc empty : . |- queue{2}

proc bit0{p} = caseR ( enq => caseR ( b0 => getR{p+2} ; L.enq ; L.b0 ; payL{p} ; bit0{p+2}
                                    | b1 => getR{p+2} ; L.enq ; L.b1 ; payL{p} ; bit0{p+2} ) )
proc bit1{p} = caseR ( enq => caseR ( b0 => getR{p+2} ; L.enq ; L.b0 ; payL{p} ; bit1{p+2}
                                    | b1 => getR{p+2} ; L.enq ; L.b1 ; payL{p} ; bit1{p+2} ) )
proc empty   = caseR ( enq => caseR ( b0 => getR{2} ; empty || bit0{2}     (* unconsumed potential *)
                                    | b1 => getR{2} ; empty || bit1{2} ) )

(*
proc ex11 : . |{9+2+4+6+8}- bits
proc ex11 = empty || L.enq ; L.b1 ; L.enq ; L.b0 ; L.enq ; L.b1 ; L.enq ; L.b1 ; L.val ; <->

exec ex11
*)
