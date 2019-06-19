#options --syntax=explicit --terminate=iso
#test error


type nat=+{mu_nat:+{s:nat, z:1}}


proc Loop: . |- nat
proc Loop= R.mu_nat;R.s; Loop


