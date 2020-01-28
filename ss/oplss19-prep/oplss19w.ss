#options --work=send --syntax=implicit
#test success

type bits = +{b0 : bits, b1 : bits, e : 1}

type ctr = &{inc : <{3}| ctr, val : <{2}| bits}

proc bit0 : ctr |{2}- ctr
proc bit1 : ctr |{3}- ctr
proc empty : . |- ctr

proc bit0 = caseR ( inc => bit1
                  | val => R.b0 ; L.val ; <-> )
proc bit1 = caseR ( inc => L.inc ; bit0
                  | val => R.b1 ; L.val ; <-> )
proc empty = caseR ( inc => empty || bit1
                   | val => R.e ; closeR )

proc three : . |{15}- bits
proc three = empty || L.inc ; L.inc ; L.inc ; L.val ; <->
exec three
