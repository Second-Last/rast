#options --work=none --syntax=explicit
#test success

type bits = +{zero : bits, one : bits, $ : 1}

type ctr = &{inc : <{3}| ctr, val : <{2}|bits}

proc bit0 : ctr |{2}- ctr
proc bit1 : ctr |{3}- ctr
proc empty : .  |{0}- ctr

proc bit0 = caseR ( inc => getR {3} ; work {2} ; bit1
                  | val => getR {2} ; work ; R.zero ; work ; L.val ; payL {2} ; <-> )

proc bit1 = caseR ( inc => getR {3} ; work ; L.inc ; payL {3} ; bit0
                  | val => getR {2} ; work ; R.one ; work ; L.val ; payL {2} ; work ; <-> )

proc empty = caseR ( inc => getR {3} ; empty || bit1
                   | val => getR {2} ; work ; R.$ ; work ; closeR )