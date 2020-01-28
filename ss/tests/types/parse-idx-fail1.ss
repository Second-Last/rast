#test error

type ctr{m} = &{inc : ctr{n+1}}

type A{m}{n} = +{l : A{m*n}{1}}