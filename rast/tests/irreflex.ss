type ctr{n} = &{inc : ctr{n+1}}

eqtype ctr{m} = ctr{n}

type A = 1

type list1{n} = +{cons : ?{n > 0}. A * list1{n-1}, nil : ?{n = 0}. 1}

type list2{n} = +{cons : ?{n > 1}. A * list2{n-2}, nil : ?{n = 0}. 1}

eqtype list1{n} = list2{2*n}

type nat{n} = +{s : ?{n > 0}. nat{n-1}, z : ?{n = 0}. 1}

type mod{x}{y} = +{s : ?{x > y-1}. mod{x-y}{y},
                    z : ?{x = 0}. 1}

eqtype nat{n} = mod{n}{1}

type even{n} = +{s : ?{n > 1}. even{n-2}, z : ?{n = 0}. 1}

eqtype nat{n} = even{2*n}

type pos{n} = +{s : ?{n > 1}. pos{n-1}, z : ?{n = 1}. 1}

eqtype nat{n} = pos{n+1}