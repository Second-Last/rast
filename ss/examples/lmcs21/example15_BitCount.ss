#options --syntax=explicit --terminate=iso
#test success

type ctr=&{nu_ctr: &{inc:ctr, val:bin}}
type bin=+{mu_bin:+{b0:bin, b1:bin, $:1}}


proc BinSucc: bin |- bin
proc BinSucc= caseL(mu_bin => caseL (b0=> R.mu_bin; R.b1; <->  
                                    | b1=> R.mu_bin; R.b0; BinSucc
                                    | $=>R.mu_bin; R.b1; R.mu_bin; R.$; w<->))

proc Counter: bin |- ctr
proc Counter= caseR(nu_ctr => caseR (inc=> BinSucc [bin] Counter
	                                | val => <->))
	                              

proc NumBits: bin |- bin
proc NumBits= caseL(mu_bin => caseL (b0=> NumBits [bin] BinSucc   
                                    | b1=> NumBits [bin] BinSucc
                                    | $=>R.mu_bin; R.$; <->))

proc BitCount: bin |- ctr
proc BitCount= NumBits;Counter
	                              
