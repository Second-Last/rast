#options --syntax=explicit
#test success

type ctr{n} = &{inc : ctr{n+1}}

type A{m}{n} = +{l : A{m*n}{n+n}}

proc bit0{n} : ctr{n} |- ctr{2*n}
proc bit0{n} = caseR (inc => bit0{n+1})
