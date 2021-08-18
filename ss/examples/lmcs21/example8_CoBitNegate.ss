#options --syntax=explicit --terminate=iso
#test success


type cobits=&{nu_cobits:+{b0:cobits, b1:cobits}}


proc CoBitNegate: cobits |- cobits
proc CoBitNegate= caseR(nu_cobits => caseR (b0=> L.nu_cobits;L.b1;CoBitNegate
	                              | b1=> L.nu_cobits;L.b0; CoBitNegate  ))


