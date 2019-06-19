#test error

type ctr{m} = &{inc : ctr}

type A{m}{n} = +{l : A{m*n}{1}}