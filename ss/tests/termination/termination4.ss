#options --syntax=explicit --terminate=iso
#test success

type ctr = &{nu_ctr : &{inc : ctr}}

proc zero : . |- ctr
proc one : ctr |- ctr

proc one = caseR ( nu_ctr =>
           caseR ( inc => L.nu_ctr ; L.inc ; one ) )
