#options --work=send --syntax=implicit
#test approx success

type ctr{n} = &{inc : <{_a*n+_aa}| ctr{n+1}, val : <{_b*n+_bb}| ubits, dec : <{_c}| +{none : ?{n = 0}. 1,
                                                                                    some : ?{n > 0}. ctr{n-1}}}

type ubits = +{b0 : ubits, $ : 1}

proc elem{n} : ctr{n} |{_d}- ctr{n+1}

proc elem{n} = caseR ( inc => L.inc ; elem{n+1}
                     | val => R.b0 ; L.val ; <->
                     | dec => R.some ; <-> )

proc empty : . |{_e}- ctr{0}

proc empty = caseR ( inc => empty || elem{0}
                   | val => R.$ ; closeR
                   | dec => R.none ; closeR )