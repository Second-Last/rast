#test error

type ctr{m} = &{inc : ctr{m+1}{4}}

type A{m}{n} = +{l : A{m*n}{1}}