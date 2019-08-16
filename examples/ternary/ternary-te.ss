#options --time=recv --syntax=explicit
#test success

(* Balanced ternary numbers, without conversion
 * to binary numbers which would require width
 * bounds or diamond to give up on precision
 *)

type ternary{r} = +{ m1 : ({r+1})ternary{r},
                     z0 : ({r+1})ternary{r},
                     p1 : ({r+1})ternary{r},
                      e : ()1 }

proc zero{r} : ternary{r}
proc zero{r} = R.e ; delay ; closeR

proc one{r} : ternary{r}
proc one{r} = R.p1 ; delay{r+1} ; R.e ; delay ; closeR

proc m_one{r} : ternary{r}
proc m_one{r} = R.m1 ; delay{r+1} ; R.e ; delay; closeR

proc neg{r} : ternary{r} |- ()ternary{r}
proc neg{r} = caseL ( m1 => R.p1 ; delay{r} ; neg{r}
                    | z0 => R.z0 ; delay{r} ; neg{r}
                    | p1 => R.m1 ; delay{r} ; neg{r}
                    | e => R.e ; waitL ; closeR )

proc copy{r} : ternary{r} |- ()ternary{r}
proc copy{r} = caseL ( m1 => R.m1 ; delay{r} ; copy{r}
                     | z0 => R.z0 ; delay{r} ; copy{r}
                     | p1 => R.p1 ; delay{r} ; copy{r}
                     | e => R.e ; waitL ; closeR )

proc inc{r} : ternary{r} |- ()ternary{r}
proc inc{r} = caseL ( m1 => R.z0 ; delay{r} ; copy{r}
                    | z0 => R.p1 ; delay{r} ; copy{r}
                    | p1 => R.m1 ; delay{r} ; inc{r}
                    | e => R.p1 ; waitL ; delay{r} ; R.e ; delay ; closeR )

proc dec{r} : ternary{r} |- ()ternary{r}
proc dec{r} = caseL ( m1 => R.p1 ; delay{r} ; dec{r}
                    | z0 => R.m1 ; delay{r} ; copy{r}
                    | p1 => R.z0 ; delay{r} ; copy{r}
                    | e => R.m1 ; waitL ; delay{r}; R.e ; delay ; closeR )


% 2*(3n-1) = 3(2*n)-2 = 3(2*n-1)+1
% 2*(3n+0) = 3(2*n)+0
% 2*(3n+1) = 3(2*n)+2 = 3(2*n+1)-1

proc dbl{r} : ternary{r} |- ()ternary{r+1}
proc dbl{r} = caseL ( m1 =>          % (r+1)ternary{r} |- ()ternary{r+1}
                                     % (r)ternary{r} |- ternary{r+1}
                             R.p1 ;  % (r)ternary{r} |- (r+2)ternary{r+1}
                             delay{r} ;         % ternary{r} |- (2)ternary{r+1}
                             dbl{r} ||          % ternary{r} |- ()ternary{r+1}
                             (delay ; dec{r+1}) % ()ternary{r+1} |- (2)ternary{r+1}
                    | z0 => R.z0 ; delay{r} ; dbl{r} || (delay ; copy{r+1})
                    | p1 => R.m1 ; delay{r} ; dbl{r} || (delay ; inc{r+1})
                    | e => R.e ; waitL ; closeR )


proc eight{r} : ternary{r}
proc eight{r} = R.m1 ; delay{r+1} ; R.z0 ; delay{r+1} ; R.p1 ; delay{r+1}; R.e ; delay ; closeR

% proc eight = one || dbl || dbl || dbl
proc eight0 : ternary{0}
proc eight0 = eight{0}
exec eight0

proc nineteen1 : ({4})ternary{1}
proc nineteen1 = eight0 || dbl{0} [({1})ternary{1}]
                 (delay{1} ; inc{1}) [({2})ternary{1}]
                 (delay{2} ; inc{1}) [({3})ternary{1}]
                 (delay{3} ; inc{1})
exec nineteen1

proc m_eight0 : ()ternary{0}
proc m_eight0 = eight0 || neg{0}
exec m_eight0

type binary{r} = +{ b0 : ({r+1})binary{r},
                    b1 : ({r+1})binary{r},
                    e : ()1 }

proc same{r} : binary{r} |- ()binary{r}
proc succ{r} : binary{r} |- ()binary{r}
proc pred{r} : binary{r} |- ()binary{r}

proc same{r} = caseL ( b0 => R.b0 ; delay{r} ; same{r}
                     | b1 => R.b1 ; delay{r}; same{r}
                     | e => R.e ; waitL ; closeR )

proc succ{r} = caseL ( b0 => R.b1 ; delay{r} ; same{r}
                     | b1 => R.b0 ; delay{r} ; same{r}
                     | e => R.b1 ; waitL ; delay{r} ; R.e ; delay ; closeR )

proc pred{r} = caseL ( b0 => R.b1 ; delay{r} ; pred{r}  % (2n+0)-1 = 2(n-1)+1
                     | b1 => R.b0 ; delay{r} ; same{r}  % may create leading b0
                     | e => R.e ; waitL ; closeR )  % 0-1 = 0, by definition

% 3*(2n+0) = 6*n   = 2(3*n)+0
% 3*(2n+1) = 6*n+3 = 2((3*n)+1)+1
% 3*0 = 0
proc times3{r} : binary{r} |- ()binary{r+1}
proc times3{r} = caseL ( b0 => R.b0 ; delay{r} ; times3{r} || delay ; same{r+1}
                       | b1 => R.b1 ; delay{r} ; times3{r} || delay ; succ{r+1}
                       | e => R.e ; waitL ; closeR )

proc six0 : binary{0}
proc six0 = R.b0 ; delay ; R.b1 ; delay ; R.b1 ; delay ; R.e ; delay ; closeR

proc eighteen_2 : ()binary{1}
proc eighteen_2 = six0 || times3{0}
exec eighteen_2

% conversion from ternary to binary
% cannot be timed without a bound
% on the width of the input number

% see file ternary-te-bdd.ss

(*
proc tern2bin : ternary |- bin
proc tern2bin = caseL ( m1 => tern2bin || times3 || pred
                      | z0 => tern2bin || times3
                      | p1 => tern2bin || times3 || succ
                      | e => R.e ; <-> )

proc eight_2 : binary
proc eight_2 = eight || tern2bin
exec eight_2

proc nineteen_2 : binary
proc nineteen_2 = nineteen || tern2bin
exec nineteen_2

proc bin2tern : binary |- ternary
proc bin2tern = caseL ( b0 => bin2tern || dbl
                      | b1 => bin2tern || dbl || inc
                      | e => R.e ; <-> )

proc nineteen_3 : ternary
proc nineteen_3 = nineteen_2 || bin2tern
exec nineteen_3

% "undefined" answer for negative ternary input
proc what : binary
proc what = m_eight || tern2bin
exec what

type sbin = +{ pos : binary, zero : binary, neg : binary }

% 3*(+n) = +(3*n)
% 3*($0) = $0
% 3*(-n) = -(3*n)
proc stimes3 : sbin |- sbin
proc stimes3 = caseL ( pos => R.pos ; times3
                     | zero => R.zero ; <->    % or R.zero ; times3
                     | neg => R.neg ; times3 )

% requires: if input = +n then n > 1
% (+n)-1 = +(n-1) for n > 1
% ($0)-1 = -(0+1)
% (-n)-1 = -(n+1)
proc spred : sbin |- sbin
proc spred = caseL ( pos => R.pos ; pred
                   | zero => R.neg ; succ
                   | neg => R.neg ; succ )

% requires: if input = -n, then n > 1
% (+n)+1 = +(n+1)
% ($0)+1 = +(0+1)
% (-n)+1 = -(n-1) for n > 1
proc ssucc : sbin |- sbin
proc ssucc = caseL ( pos => R.pos ; succ
                   | zero => R.pos ; succ
                   | neg => R.neg ; pred )

% $0
proc szero : sbin
proc szero = R.zero ; R.e ; closeR

proc tern2sbin : ternary |- sbin
proc tern2sbin = caseL ( m1 => tern2sbin || stimes3 || spred
                       | z0 => tern2sbin || stimes3
                       | p1 => tern2sbin || stimes3 || ssucc
                       | e => waitL ; szero )

proc nineteen_s2 : sbin
proc nineteen_s2 = nineteen_3 || tern2sbin
exec nineteen_s2

proc m_eight_s2 : sbin
proc m_eight_s2 = m_eight || tern2sbin
exec m_eight_s2

% could also split bin2tern into bin2tern_pos and bin2tern_neg
proc sbin2tern : sbin |- ternary
proc sbin2tern = caseL ( pos => bin2tern
                       | zero => bin2tern
                       | neg => bin2tern || neg )

proc sneg : sbin |- sbin
proc sneg = caseL ( pos => R.neg ; <->
                  | zero => R.zero ; <->
                  | neg => R.pos ; <-> )

proc m_nineteen : ternary
proc m_nineteen = nineteen_s2 || sneg || sbin2tern
exec m_nineteen
*)
