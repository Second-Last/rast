#options --work=send --syntax=implicit
#test success

type bits = +{b0 : bits, b1 : bits, $ : 1}

type queue{p} = &{enq : &{b0 : <p| queue{p+2}, b1 : <p| queue{p+2}},
                  val : <|<| bits}

proc bit0 : queue{p} |{2}- queue{p+2}
proc bit1 : queue{p} |{2}- queue{p+2}
proc empty : . |{2}- queue{2}

proc bit0 = caseR ( enq => caseR ( b0 => L.enq ; L.b0 ; bit0
                                 | b1 => L.enq ; L.b1 ; bit0 )
                  | val => R.b0 ; L.val ; <-> )
proc bit1 = caseR ( enq => caseR ( b0 => L.enq ; L.b0 ; bit1
                                 | b1 => L.enq ; L.b1 ; bit1 )
                  | val => R.b1 ; L.val ; <-> )
proc empty = caseR ( enq => caseR ( b0 => empty || bit0
                                  | b1 => empty || bit1 )
                   | val => R.$ ; closeR )

proc ex11 : . |{9+2+4+6+8}- bits
proc ex11 = empty || L.enq ; L.b1 ; L.enq ; L.b0 ; L.enq ; L.b1 ; L.enq ; L.b1 ; L.val ; <->

exec ex11
