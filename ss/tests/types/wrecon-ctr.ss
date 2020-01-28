#options --work=send --syntax=implicit
#test success

type ctr{n} = &{inc : <{n+1}| ctr{n+1}, dec : <{2}| +{none : ?{n = 0}. 1,
                                                    some : ?{n > 0}. ctr{n-1}}}
                                        
proc elem{n} : ctr{n} |- ctr{n+1}

proc elem{n} = caseR ( inc => L.inc ; elem{n+1}
                     | dec => R.some ; <-> )

proc empty : ctr{0}

proc empty = caseR ( inc => empty || elem{0}
                   | dec => R.none ; closeR )