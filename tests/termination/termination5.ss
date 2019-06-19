#options --syntax=explicit --terminate=iso
#test success

type nat = +{mu_nat : +{z : 1, s : nat}}

proc copy : nat |- nat
proc copy = caseL ( mu_nat =>
            caseL ( z => R.mu_nat ; R.z ; waitL ; closeR
                  | s => R.mu_nat ; R.s ; copy )
                   )

