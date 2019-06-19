#options --work=send --syntax=explicit

type ctr = &{inc : <| ctr}

proc bit0 : ctr |- ctr
proc bit1 : ctr |{1}- ctr
proc empty : .  |- ctr

proc bit0 = caseR ( inc => getR ; bit1 )

proc bit1 = caseR ( inc => getR ; L.inc ; payL ; bit0 )

proc empty = caseR ( inc => getR ; empty || bit1 )

proc three : . |{6}- ctr

proc three = empty || L.inc ; payL ; L.inc ; payL ; L.inc ; payL ; <->

exec three