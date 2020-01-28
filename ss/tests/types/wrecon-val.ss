#options --work=send --syntax=implicit
#test success

type ctr{n} = &{inc : <{n}| ctr{n+1}, val : <{2*n+2}| ubits, dec : <{2}| +{none : ?{n = 0}. 1,
                                                                       some : ?{n > 0}. ctr{n-1}}}

type ubits = +{b0 : ubits, $ : 1}

proc elem{n} : ctr{n} |- ctr{n+1}

proc elem{n} = caseR ( inc => L.inc ; elem{n+1}
                     | val => R.b0 ; L.val ; <->
                     | dec => R.some ; <-> )

proc empty : ctr{0}

proc empty = caseR ( inc => empty || elem{0}
                   | val => R.$ ; closeR
                   | dec => R.none ; closeR )