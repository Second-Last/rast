#options --work=send --syntax=implicit
#test error

type nat = +{z : |> 1,
             s : nat}

proc imp : nat |- nat
proc imp = caseL (z => R.z ; <-> | s => imp)
