#options --syntax=explicit

type bits = +{b0 : bits, b1 : bits, e : 1}

type ctr{n} = &{inc : ctr{n+1},
                val : bits}

proc bit0{n} : ctr{n} |- ctr{2*n}
proc bit1{n} : ctr{n} |- ctr{2*n+1}
proc empty : ctr{0}

proc empty = caseR ( inc => empty || bit1{0}
                   | val => R.e ; closeR )
proc bit0{n} = caseR ( inc => bit1{n}
                     | val => L.val ; R.b0 ; <-> )
proc bit1{n} = caseR ( inc => L.inc ; bit0{n+1}
                     | val => L.val ; R.b1 ; <-> )

proc plus1{n} : ctr{n} |- ctr{n+1}
proc plus1{n} = L.inc ; <->

proc six : ctr{6}
proc six = empty || plus1{0} || L.inc ; L.inc ; L.inc ; L.inc ; L.inc ; <->

exec six

proc seven : bits
proc seven = six || L.inc ; L.val ; <->
exec seven

