#options --syntax=explicit --terminate=iso
#test error


type nat=+{mu_nat:+{s:nat, z:1}}


proc Block: nat |- 1
proc Block= caseL(mu_nat => caseL (z=> waitL; closeR
	                              | s=> Block ))

