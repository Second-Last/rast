#options --syntax=implicit
#test error

type nat{n} = +{z : ?{n = 0}. 1, s : ?{n > 0}. nat{n-1} }
%type succ {n | n > 0} = nat{n-1}

proc pred{n | n >= 0} : nat{n} |- nat{n-1}
proc pred{n} = caseL (s => <->)
