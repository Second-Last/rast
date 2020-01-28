#test error

type ctr{n} = &{inc : ctr{0}}

type A{m}{n} = +{l : A{m*n}{1}}

proc inc{k} : . |- ctr{k}
proc inc{n} = caseR (inc => getR{k} ; <->)
