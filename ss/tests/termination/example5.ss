#options --syntax=explicit --terminate=iso
#test success


type bits=+{mu_bits:+{b0:bits, b1:bits}}


proc BitNegate: bits |- bits
proc BitNegate= caseL(mu_bits => caseL (b0=> R.mu_bits;R.b1;BitNegate
	                              | b1=> R.mu_bits;R.b0; BitNegate  ))


