#options --syntax=explicit --terminate=iso
#test error

% terminates, but fails test
% see TuringUnary.ss for better version

type epat= &{nu_epat: &{eone:epat, estar:epat, emiddle:epat, eend:tape}}
type tape=  +{mu_tape: +{tone:tape, tstar:tape, tmiddle:tape, tend:1}}


proc Zero: tape |- tape 
proc Zero= Ze [epat] (L.nu_epat;L.eend; <->)


proc Ze: tape |- epat
proc Ze= caseL (mu_tape =>caseL(tone=> Ze
                               |tstar=> Ze [epat] L.nu_epat;L.estar; <->
                               |tmiddle=> Ze [epat] L.nu_epat;L.emiddle; <->
                               |tend=>  (R.mu_tape;R.tend; <->)  [tape] Final))

proc Final: tape |- epat
proc Final= caseR (nu_epat => caseR (eone=> (R.mu_tape;R.tone; <->) [tape] Final
                                     |estar=> (R.mu_tape;R.tstar; <->) [tape] Final
                                     |emiddle=> (R.mu_tape;R.tmiddle; <->) [tape] Final
                                     |eend=>   <->))

proc ZeroTest : tape
proc ZeroTest = (R.mu_tape; R.tone; R.mu_tape; R.tone; R.mu_tape; R.tend; closeR) [tape] Zero
exec ZeroTest
