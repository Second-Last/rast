#options --syntax=explicit --terminate=iso
#test success



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

%unary composition

proc ComposeGF:tape|-tape
proc ComposeGF= G [tape] F

% needs to be defined to ComposeGF
proc G : tape |- tape
proc G = Succ 

proc F : tape |- tape
proc F = Succ [tape] RecursionH 


% Tests

% 11|1 => .
proc ZeroTest : tape
proc ZeroTest = (R.mu_tape; R.tone; R.mu_tape; R.tone;
                 R.mu_tape; R.tmiddle; R.mu_tape; R.tone;
                 R.mu_tape ; R.tend; closeR) [tape] Zero
exec ZeroTest

% . => 11
proc SuccTest : tape
proc SuccTest = ZeroTest [tape] Succ [tape] Succ 
exec SuccTest

% 11|1 => 11
proc Proj1Test : tape
proc Proj1Test = (R.mu_tape; R.tone; R.mu_tape; R.tone;
                 R.mu_tape; R.tmiddle; R.mu_tape; R.tone;
                 R.mu_tape ; R.tend; closeR)  [tape] Project1
exec Proj1Test

% 11|. => 1111 (double first arg, add second)
proc RecursionHTest : tape
proc RecursionHTest = SuccTest [tape] RecursionH
exec RecursionHTest

% 11 => 111 => 1111 => 11111111 (??)
proc ComposeGFTest : tape
proc ComposeGFTest = SuccTest [tape] ComposeGF
exec ComposeGFTest

