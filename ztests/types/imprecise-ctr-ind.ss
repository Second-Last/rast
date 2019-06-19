#options --work=send --syntax=explicit
#test success

type bits = +{b0 : bits, b1 : bits, $ : bits}

type ctr{n} = &{inc : <{n}| ctr}

proc bit0{n} : ctr{n} |- ctr{2*n}
proc bit1{n} : ctr{n} |- ctr{2*n+1}
proc empty : .  |- ctr{0}

proc bit0{n} = caseR ( inc => getR {2*n} ; work {2*n} ; bit1{n} )

proc bit1{n} = caseR ( inc => getR {2*(n+1)} ; work ; L.inc ; payL {n} ; work {n} ; bit0{n+1} )

proc empty = caseR ( inc => getR {0} ; empty || bit1{1} )

proc three : . |{6}- ctr

proc three = empty || work ; L.inc ; payL {0} ; work ; L.inc ; payL {1} ; work ; L.inc ; payL {2} ; <->

exec three