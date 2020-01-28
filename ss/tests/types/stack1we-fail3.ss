#options --syntax=explicit
#test error

type bits = +{b0 : bits, b1 : bits}

type stack{n} = &{ins : &{b0 : stack{n+1}, b1 : stack{n+1}},
                  del : +{none : ?{n = 0}. 1,
                          some : ?{n > 0}. +{b0 : stack{n-1}, b1 : stack{n-1}}}}

proc bit0{n} : stack{n} |- stack{n+1}
proc bit1{n} : stack{n} |- stack{n+1}
proc empty : stack{0}

proc bit0{n} = caseR ( ins => caseR ( b0 => bit0{n} || bit0{n+1}
                                    | b1 => bit0{n} || bit1{n+1})
                     | del => R.some ; assertR {n+1 > 0} ; R.b0 ; <-> )

proc bit1{n} = caseR ( ins => caseR ( b0 => bit1{n} || bit0{n+1}
                                    | b1 => bit1{n} || bit1{n+1})
                     | del => R.some ; assertR {n+1 > 0} ; R.b1 ; <-> )

proc empty = caseR ( ins => caseR ( b0 => empty || bit0{0}
                                  | b1 => empty || bit1{0} )
                   | del => R.some ; assertR {0+1 > 0} ; <-> )