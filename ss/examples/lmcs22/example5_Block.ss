#options --syntax=explicit --terminate=iso
#test success


type nat=+{mu_nat:+{s:nat, z:1}}


proc Block: nat |- 1
proc Block= caseL(mu_nat => caseL ( s=>Block
                                  | z=> waitL; closeR))
	                           

