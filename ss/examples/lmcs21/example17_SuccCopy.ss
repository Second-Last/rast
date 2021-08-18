#options --syntax=explicit --terminate=iso
#test error


type nat=+{mu_nat:+{z:1, s:nat}}


proc Succ_Copy: nat |- nat
proc Succ_Copy= Succ [nat] Bogus_Copy

proc Succ: nat |- nat
proc Succ= R.mu_nat; R.s;<->
	                              
proc Bogus_Copy: nat |- nat
proc Bogus_Copy= caseL(mu_nat => caseL (z=> R.mu_nat;R.z;waitL; closeR
	                              | s=> R.mu_nat;R.s; Succ_Copy ))


