#options --work=send --syntax=implicit
#test approx success

type ctr = &{inc : <{_a}| ctr}

proc bit0 : ctr |{_b}- ctr
proc bit1 : ctr |{_c}- ctr
proc empty : .  |{_d}- ctr

proc bit0 = caseR ( inc => bit1 )

proc bit1 = caseR ( inc => L.inc ; bit0 )

proc empty = caseR ( inc => empty || bit1 )

proc three : . |{_e}- ctr

proc three = empty || L.inc ; L.inc ; L.inc ; <->

(*exec three*)