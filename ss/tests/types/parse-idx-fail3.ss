#test error

type ctr{m+n} = &{inc : ctr{m+1}}

type A{m}{n} = +{l : A{m*n}{1}}