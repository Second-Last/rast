#options --work=send --syntax=explicit
#test error

type stack{n} = &{ins : &{b0 : stack{n+1}, b1 : stack{n+1}},
                  del : <{2}| +{none : ?{n = 0}. 1,
                          some : ?{n > 0}. +{b0 : stack{n-1}, b1 : stack{n-1}}}}

proc bit0{n} : stack{n} |- stack{n+1}
proc bit1{n} : stack{n} |- stack{n+1}
proc empty : stack{0}

proc bit0{n} = caseR ( ins => caseR ( b0 => bit0{n} || bit0{n+1}
                                    | b1 => bit0{n} || bit1{n+1})
                     | del => getR {2} ; R.some ; assertR {n+1 > 0} ; R.b0 ; <-> )

proc bit1{n} = caseR ( ins => caseR ( b0 => bit1{n} || bit0{n+1}
                                    | b1 => bit1{n} || bit1{n+1})
                     | del => getR {2} ; R.some ; assertR {n+1 > 0} ; R.b1 ; <-> )

proc empty = caseR ( ins => caseR ( b0 => empty || bit0{0}
                                  | b1 => empty || bit1{0} )
                   | del => getR {2} ; R.none ; assertR {0 = 0} ; closeR )

proc delclient{n}{k} : stack{n+4} |{4+4+4+4}- stack{k}

proc delclient{n}{k} = L.del ; payL {2} ; caseL ( none => impossibleL{n+4 = 0}
                                                | some => assumeL{n+4 > 0} ; caseL ( b0 => delclient{n-1}{k}
                                                                                   | b1 => delclient{n-1}{k} ))