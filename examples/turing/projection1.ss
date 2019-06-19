#options --syntax=explicit --terminate=iso
#test success

% terminates, but this particular formulation doesn't check
% for better one see TuringUnary.ss

type epat= &{nu_epat: &{eone:epat, estar:epat, emiddle:epat, eend:tape}}
type tape=  +{mu_tape: +{tone:tape, tstar:tape, tmiddle:tape, tend:1}}


proc Project1: tape |- tape
proc Project1= caseL( mu_tape=> caseL( tone=> Project1 [tape] R.mu_tape; R.tone; <->
                                       |tstar => Project1 [tape] R.mu_tape; R.tstar; <->
                                       |tmiddle => Deleterest
                                       |tend=> R.mu_tape; R.tend; <->))
proc Deleterest:tape |- tape
proc Deleterest=caseL( mu_tape=> caseL( tone=> Deleterest
                                       |tstar => Deleterest
                                       |tmiddle => Deleterest
                                       |tend=> R.mu_tape; R.tend; <->))
 
