#options --syntax=explicit --terminate=iso
#test error

% does not terminate

type tape=  +{mu_tape: +{tone:tape, tstar:tape, tmiddle:tape, tend:1}}
type epat= &{nu_epat: &{eone:epat, estar:epat, emiddle:epat, eend:tape}}


proc Zero: tape |- tape 
proc Zero= Ze [epat] (L.nu_epat;L.eend; <->)


proc Ze: tape |- epat
proc Ze= caseL (mu_tape =>caseL(tone=> Ze
                               |tstar=> Ze 
                               |tmiddle=> Ze 
                               |tend=>  (R.mu_tape;R.tend; <->)  [tape] Reset))

proc Reset: tape |- epat
proc Reset= caseR (nu_epat => caseR (eone=>  Reset
                                     |estar=>  Reset
                                     |emiddle=>  Reset
                                     |eend=>   <->))

% Succ

proc Succ: tape |- tape 
proc Succ= R.mu_tape; R.tone; <->

% Projection1

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
 
% Recursion

proc RecursionH: tape |- tape
proc RecursionH= caseL( mu_tape=> caseL( tone=> RecursionH [tape] H
                                       |tstar => RecursionH [tape] H
                                       |tmiddle => <->
                                       |tend=> R.mu_tape; R.tend; <->))

% needs to be defined to run RecursionH
% example: double the number
proc H : tape |- tape
proc H = Succ [tape] Succ

% Copy

proc Copy: tape |-tape
proc Copy= eCopy [epat] L.nu_epat; L.eend; <->
	
proc eCopy: tape |- epat
proc eCopy=  caseL( mu_tape=> caseL( tone=>gotoend [epat] L.nu_epat; L.estar; L.nu_epat; L.eone; <->
                                       |tstar => gotoend [epat] L.nu_epat; L.estar; L.nu_epat; L.eone; <->
                                       |tmiddle => gotoendmid [epat] L.nu_epat; L.estar; L.nu_epat; L.emiddle; <->
                                       |tend=> outputend [tape] Final))

proc gotoend: tape |- epat
proc gotoend=  caseL( mu_tape=> caseL( tone=>gotoend [epat] L.nu_epat; L.eone; <->
                                       |tstar => gotoend [epat] L.nu_epat; L.estar; <->
                                       |tmiddle => gotoend [epat]  L.nu_epat; L.emiddle; <->
                                       |tend=> gotoendfin [tape] Final))

proc gotoendfin: 1|-tape
proc gotoendfin= R.mu_tape; R.tstar; R.mu_tape; R.tmiddle; R.mu_tape; R.tone; R.mu_tape; R.tend; <->

proc gotoendfin2: 1|-tape
proc gotoendfin2= R.mu_tape; R.tone; R.mu_tape; R.tend; <->
 
proc gotoendmid: tape |- epat
proc gotoendmid=  caseL( mu_tape=> caseL( tone=>gotoendmid [epat] L.nu_epat; L.eone; <->
                                       |tstar => gotoendmid [epat] L.nu_epat; L.estar; <->
                                       |tmiddle => gotoendmid [epat]  L.nu_epat; L.emiddle; <->
                                       |tend=> gotoendmidfin [tape] Final))

proc gotoendmidfin: 1|-tape
proc gotoendmidfin= R.mu_tape; R.tstar; R.mu_tape; R.tmiddle; R.mu_tape; R.tmiddle; R.mu_tape; R.tend; <->

proc gotoendmidfin2: 1|-tape
proc gotoendmidfin2= R.mu_tape; R.tmiddle; R.mu_tape; R.tend; <->

proc outputend: 1 |- tape
proc outputend= R.mu_tape; R.tmiddle; R.mu_tape; R.tend; <->





proc eCopy2: tape|-epat
proc eCopy2= caseL( mu_tape=> caseL( tone=>gotoend2 [epat] L.nu_epat; L.estar; L.nu_epat; L.eone; <->
                                       |tstar => Final [epat] L.nu_epat; L.estar;<->  %not terminating
                                       |tmiddle => gotoendmid2 [epat] L.nu_epat; L.estar; L.nu_epat; L.emiddle; <->
                                       |tend=> outputend [tape] Final))


proc gotoend2: tape |- epat
proc gotoend2=  caseL( mu_tape=> caseL( tone=>gotoend2 [epat] L.nu_epat; L.eone; <->
                                       |tstar => gotoends [epat] L.nu_epat; L.estar; <->
                                       |tmiddle => gotoend2 [epat]  L.nu_epat; L.emiddle; <->
                                       |tend=> gotoendfin2 [tape] Final2))

proc gotoendmid2: tape |- epat
proc gotoendmid2=  caseL( mu_tape=> caseL( tone=>gotoendmid2 [epat] L.nu_epat; L.eone; <->
                                       |tstar => gotoendmids [epat] L.nu_epat; L.estar; <->
                                       |tmiddle => gotoendmid2 [epat]  L.nu_epat; L.emiddle; <->
                                       |tend=> gotoendmidfin2 [tape] Final2))

proc gotoends: tape |- epat
proc gotoends=  caseL( mu_tape=> caseL( tone=>gotoends [epat] L.nu_epat; L.eone; <->
                                       |tstar => gotoendmids [epat] L.nu_epat; L.estar; <->
                                       |tmiddle => gotoends [epat]  L.nu_epat; L.emiddle; <->
                                       |tend=> gotoendfin2 [tape] Final2))

proc gotoendmids: tape |- epat
proc gotoendmids=  caseL( mu_tape=> caseL( tone=>gotoendmids [epat] L.nu_epat; L.eone; <->
                                       |tstar => gotoendmids [epat] L.nu_epat; L.estar; <->
                                       |tmiddle => gotoendmids [epat]  L.nu_epat; L.emiddle; <->
                                       |tend=> gotoendmidfin2 [tape] Final2))


proc Final: tape |-epat
proc Final= caseR (nu_epat => caseR (eone=> (R.mu_tape;R.tone; <->) [tape] Final
                                     |estar=> (R.mu_tape;R.tstar; <->) [tape] eCopy2 %not terminating
                                     |emiddle=> (R.mu_tape;R.tmiddle; <->) [tape] Final
                                     |eend=>   <->))

proc Final2: tape |-epat
proc Final2= caseR (nu_epat => caseR (eone=> (R.mu_tape;R.tone; <->) [tape] Final2
                                     |estar=> (R.mu_tape;R.tstar; <->) [tape] Final
                                     |emiddle=> (R.mu_tape;R.tmiddle; <->) [tape] Final2
                                     |eend=>   <->))


% Tests

% 11|1 => .|.
proc ZeroTest : tape
proc ZeroTest = (R.mu_tape; R.tone; R.mu_tape; R.tone;
                 R.mu_tape; R.tmiddle; R.mu_tape; R.tone;
                 R.mu_tape ; R.tend; closeR) [tape] Zero
exec ZeroTest

% .|. => 11|.
proc SuccTest : tape
proc SuccTest = ZeroTest [tape] Succ [tape] Succ 
exec SuccTest

% 11|. => 11
proc Proj1Test : tape
proc Proj1Test = SuccTest [tape] Project1
exec Proj1Test

% 11|. => 1111 (double first arg, add second)
proc RecursionHTest : tape
proc RecursionHTest = SuccTest [tape] RecursionH
exec RecursionHTest

% 1111 => 1111|1111 (??)
proc CopyTest : tape
proc CopyTest = RecursionHTest [tape] Copy
exec CopyTest

% 1111|1111 => 111111111111 (??)
proc AllTest : tape
proc AllTest = CopyTest [tape] RecursionH
exec AllTest
