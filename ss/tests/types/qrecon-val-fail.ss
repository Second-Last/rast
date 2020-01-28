#options --syntax=implicit
#test error

type ctr{n} = &{inc : ctr{n+1}, val : ubits, dec : +{none : ?{n = 0}. 1,
                                                     some : ?{n > 0}. ctr{n-1}}}

type ubits = +{b0 : ubits, $ : 1}

proc elem{n} : ctr{n} |- ctr{n+1}

proc elem{n} = caseR ( inc => L.inc ; elem{n+1}
                     | val => R.b0 ; L.val ; <-> )

proc empty : ctr{0}

proc empty = caseR ( inc => empty || elem{0}
                   | val => R.$ ; closeR )