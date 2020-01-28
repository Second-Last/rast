#options --syntax=implicit
#test success

type nat{n} = +{z : ?{n = 0}. 1, s : ?{n > 0}. nat{n-1}}

type ubits = +{b0 : ubits, $ : 1}

proc convert{n} : nat{n} |- ubits

proc convert{n} = caseL ( z => R.$ ; <->
                        | s => R.b0 ; convert{n-1})
