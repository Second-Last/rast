#options --syntax=explicit
#test error

type nat{n} = +{z : ?{n = 0}. 1, s : ?{n >}. nat{n-1}}

proc inc{n} : nat{n} |- nat{n+1}

proc inc{n} = R.s ; assertR {n+1 > 0} ; <->

proc rinc{n} : nat{n} |- nat{n+1}

proc rinc{n} = caseL ( z => assumeL {n = 0} ; waitL ; R.s ; assertR {0+1 > 0} ; R.z ; assertR {0 = 0} ; closeR
                     | s => assumeL {n > 0} ; R.s ; assertR{n+1 > 0} ; rinc{n-1} )