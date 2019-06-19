#options --syntax=explicit

type ctr{n} = &{inc : ctr{n+1}}

proc bit0{n} : ctr{n} |- ctr{2*n}
proc bit1{n} : ctr{n} |- ctr{2*n+1}
proc empty : ctr{0}

proc empty = caseR ( inc => empty || bit1{0} )
proc bit0{n} = caseR ( inc => bit1{n} )
proc bit1{n} = caseR ( inc => L.inc ; bit0{n+1} )
