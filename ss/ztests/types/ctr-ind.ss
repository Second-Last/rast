#options --work=send --syntax=explicit
#test success

type bits = +{b0 : bits, b1 : bits, $ : bits}

type ctr{n} = &{inc : <| ctr, val : <{2*ceil(log(n+1))+2}| bits}

proc bit0{n} : ctr{n} |- ctr{2*n}
proc bit1{n} : ctr{n} |{1}- ctr{2*n+1}
proc empty : .  |- ctr{0}

proc bit0{n} = caseR ( inc => getR ; bit1
                     | val => getR {2*ceil(log(2*n+1))+2} ; work ; R.b0 ; 
                              work ; L.val ; payL {2*ceil(log(n+1))+2} ; <-> )

proc bit1{n} = caseR ( inc => getR ; L.inc ; payL ; bit0
                     | val => getR {2*ceil(log(2*n+2))+2} ; work ; R.b1 ;
                              work ; L.val ; payL {2*ceil(log(n+1))+2} ; <-> )

proc empty = caseR ( inc => getR ; empty || bit1
                   | val => getR {2} ; work ; R.$ ; work ; closeR )

proc three : . |{6}- ctr

proc three = empty || L.inc ; payL ; L.inc ; payL ; L.inc ; payL ; <->

exec three