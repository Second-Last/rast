#options --syntax=implicit
#test error

type nat{n} = +{z : ?{n = 0}. 1,
                s : ?{n > 0-1}. nat{n}}

proc imp : nat{0} |- 1
proc imp = caseL (z => <->)


