#options --syntax=explicit --terminate=iso
#test success

type tape=  +{mu_tape: +{tone:tape, tstar:tape, tmiddle:tape, tend:1}}
type epat= &{nu_epat: &{eone:epat, estar:epat, emiddle:epat, eend:tape}}


proc Recursion: tape |- tape
proc Recursion= caseL( mu_tape=> caseL( tone=> Recursion [tape] Succ
                                       |tstar => Recursion [tape] Succ
                                       |tmiddle => <->
                                       |tend=> R.mu_tape; R.tend; <->))



proc Succ: tape |- tape 
proc Succ= R.mu_tape; R.tone; <->
 
