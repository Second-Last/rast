#options --work=send --syntax=implicit
#test approx success

type nat{n} = +{z : ?{n = 0}. |{_a*n+_aa}> 1, s : ?{n > 0}. |{_b*n+_bb}> nat{n-1}}

type ubits = +{b0 : ubits, $ : 1}

proc convert{n} : nat{n} |{_c}- ubits

proc convert{n} = caseL ( z => R.$ ; <->
                        | s => R.b0 ; convert{n-1})