#test approx success

type ctr{n} = &{inc : ctr{0}}

type A{m}{n} = +{l : A{m*n}{1}}

proc inc{n} : . |- ctr{n}
