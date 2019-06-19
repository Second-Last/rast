#options --syntax=explicit --terminate=iso
#test success

type nat = +{mu_nat : +{z : 1, s : nat}}
type stream = &{nu_stream : &{head : nat, next : stream}}

proc consume : nat |- 1
proc consume = caseL (mu_nat => caseL ( z => waitL ; closeR
                                      | s => consume ) )
