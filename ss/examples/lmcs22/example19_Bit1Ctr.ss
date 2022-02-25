#options --syntax=explicit --terminate=iso
#test error


type ctr=&{nu_ctr: &{inc:ctr, val:bin}}
type bin=+{mu_bin:+{b0:bin, b1:bin, $:1}}

proc Bit0Ctr: ctr |- ctr
proc Bit0Ctr= caseR(nu_ctr => caseR (inc=> Bit1Ctr
	                                | val => R.mu_bin; R.b0; L.nu_ctr; L.val; <->))
	                              
proc Bit1Ctr: ctr |- ctr
proc Bit1Ctr= caseR(nu_ctr => caseR (inc=> L.nu_ctr; L.inc; Bit0Ctr
	                                | val => R.mu_bin; R.b1; L.nu_ctr; L.val; <->))
	                              
proc Empty:  . |- ctr
proc Empty= caseR(nu_ctr => caseR (inc=> Empty [ctr] Bit1Ctr
	                              | val => R.mu_bin; R.$; closeR))

