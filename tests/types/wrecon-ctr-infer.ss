#options --work=send --syntax=implicit
#test approx success

type ctr{n} = &{inc : <{_a*n+_aa}| ctr{n+1}, dec : <{_b}| +{none : ?{n = 0}. 1,
                                                    some : ?{n > 0}. ctr{n-1}}}
                                        
proc elem{n} : ctr{n} |{_c}- ctr{n+1}

proc elem{n} = caseR ( inc => L.inc ; elem{n+1}
                     | dec => R.some ; <-> )

proc empty : . |{_d}- ctr{0}

proc empty = caseR ( inc => empty || elem{0}
                   | dec => R.none ; closeR )