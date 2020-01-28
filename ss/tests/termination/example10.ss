#options --syntax=explicit --terminate=iso
#test success

type ack=+{mu_ack: +{ack:astream}}
type astream=&{nu_astream: &{head:ack, tail:astream}}
type nat=+{mu_nat:+{z:1, s:nat}}


proc Producer: astream |- nat
proc Producer= L.nu_astream; L.head; Idle

proc Idle: ack |- nat
proc Idle= caseL(mu_ack => caseL (ack=> R.mu_nat;R.s;Producer))
	                              


