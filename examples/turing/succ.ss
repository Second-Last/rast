#options --syntax=explicit --terminate=iso
#test success

type epat= &{nu_epat: &{eone:epat, estar:epat, emiddle:epat, eend:tape}}
type tape=  +{mu_tape: +{tone:tape, tstar:tape, tmiddle:tape, tend:1}}

proc Succ: tape |- tape 
proc Succ= R.mu_tape; R.tone; <->

