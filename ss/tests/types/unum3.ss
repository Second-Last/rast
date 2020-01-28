#options --syntax=explicit
#test success

type nat{n} = +{z : ?{n = 0}. 1, s : ?{n > 0}. nat{n-1}}

proc dec{n} : nat{n+1} |- nat{n}
proc dec{n} = caseL ( z => impossibleL {n+1 = 0}
                    | s => assumeL {n+1 > 0} ; <-> )
