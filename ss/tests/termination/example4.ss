#options --syntax=explicit --terminate=iso
#test success


type nat=+{mu_nat:+{z:1, s:nat}}


proc Copy: nat |- nat
proc Copy= caseL(mu_nat => caseL (z=> R.mu_nat;R.z;waitL; closeR
	                              | s=> R.mu_nat;R.s; Copy ))


