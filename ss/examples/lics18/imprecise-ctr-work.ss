#options --work=none --syntax=explicit

type bits = +{zero : bits, one : bits, $ : 1}

type ctr = &{inc : <|<|<|ctr, val : <|<|bits}

proc bit0 : ctr |{2}- ctr
proc bit1 : ctr |{3}- ctr
proc empty : .  |- ctr

proc bit0 = caseR ( inc => getR ; getR ; getR ; work ; work ; bit1
                  | val => getR ; getR ; work ; R.zero ; work ; L.val ; payL ; payL ; <-> )

proc bit1 = caseR ( inc => getR ; getR ; getR ; work ; L.inc ; payL ; payL ; payL ; bit0
                  | val => getR ; getR ; work ; R.one ; work ; L.val ; payL ; payL ; work ; <-> )

proc empty = caseR ( inc => getR ; getR ; getR ; empty || bit1
                   | val => getR ; getR ; work ; R.$ ; work ; closeR )