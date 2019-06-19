#options --syntax=explicit --terminate=iso
#test error

% terminates, but shouldn't check

type epat= &{nu_epat: &{eone:epat, estar:epat, emiddle:epat, eend:tape}}
type tape=  +{mu_tape: +{tone:tape, tstar:tape, tmiddle:tape, tend:1}}

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




proc Final: tape |-epat
proc Final= caseR (nu_epat => caseR (eone=> (R.mu_tape;R.tone; <->) [tape] Final
                                     |estar=> eCopy2
                                     |emiddle=> (R.mu_tape;R.tmiddle; <->) [tape] Final
                                     |eend=>   <->))

proc Final2: tape |-epat
proc Final2= caseR (nu_epat => caseR (eone=> (R.mu_tape;R.tone; <->) [tape] Final2
                                     |estar=> (R.mu_tape;R.tstar; <->) [tape] Final
                                     |emiddle=> (R.mu_tape;R.tmiddle; <->) [tape] Final2
                                     |eend=>   <->))


proc eCopy2: tape|-epat
proc eCopy2= caseL( mu_tape=> caseL( tone=>gotoend2 [epat] L.nu_epat; L.estar; L.nu_epat; L.eone; <->
                                       |tstar => Final
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




