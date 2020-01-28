#options --time=recv --syntax=implicit
#test success

type nat = +{z : `1, s : `nat}

proc pred : nat |- ()nat
proc pred = caseL (z => R.z ; waitL ; closeR | s => <->)

proc two : nat
proc two = R.s ; R.s ; R.z ; closeR
exec two

proc one : ()nat
proc one = two || pred
exec one
