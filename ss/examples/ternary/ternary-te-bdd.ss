#options --time=free --syntax=explicit
#test approx success

(* Balanced ternary representation with parallel time,
 * achieved by bounding the size of ternary numbers.
 * The size estimates are not very tight, but tighter
 * bounds may be difficult to achieve.
 *
 * Some bounds are nonlinear (for conversion from balanced
 * ternary to binary form).
 *)

(* 
 * Here, need to state --time=free because otherwise
 * the "constraints" interfere with the timing.  We
 * insert a "tick" after each receive wehere it can be placed
 * without interfering with the rigid timing constraints
 *)

type ternary{r}{w} = +{ m1 : ?{w>0}. ({r+1})ternary{r}{w-1},
                        z0 : ?{w>0}. ({r+1})ternary{r}{w-1},
                        p1 : ?{w>0}. ({r+1})ternary{r}{w-1},
                         e : ()1 }

proc zero{r}{w | w >= 0} : ternary{r}{w}
proc zero{r}{w} = R.e ; delay ; closeR

proc one{r}{w | w >= 1} : ternary{r}{w}
proc one{r}{w} = R.p1 ; assertR {w > 0}; delay{r+1} ; R.e ; delay ; closeR

proc m_one{r}{w | w >= 1} : ternary{r}{w}
proc m_one{r}{w} = R.m1 ; assertR {w > 0}; delay{r+1} ; R.e ; delay; closeR

proc neg{r}{w} : ternary{r}{w} |- ()ternary{r}{w}
proc neg{r}{w} = caseL ( m1 => assumeL{w>0}; tick ; R.p1 ; assertR{w>0}; delay{r} ; neg{r}{w-1}
                       | z0 => assumeL{w>0}; tick ; R.z0 ; assertR{w>0}; delay{r} ; neg{r}{w-1}
                       | p1 => assumeL{w>0}; tick ; R.m1 ; assertR{w>0}; delay{r} ; neg{r}{w-1}
                       | e => tick ; R.e ; waitL ; tick ; closeR )

proc copy{r}{w}{v|v>w} : ternary{r}{w} |- ()ternary{r}{v}
proc copy{r}{w}{v} = caseL ( m1 => assumeL{w>0}; tick; R.m1 ; assertR{v>0}; delay{r} ; copy{r}{w-1}{v-1}
                           | z0 => assumeL{w>0}; tick; R.z0 ; assertR{v>0}; delay{r} ; copy{r}{w-1}{v-1}
                           | p1 => assumeL{w>0}; tick; R.p1 ; assertR{v>0}; delay{r} ; copy{r}{w-1}{v-1}
                           | e => tick ; R.e ; waitL ; tick ; closeR )

proc inc{r}{w} : ternary{r}{w} |- ()ternary{r}{w+1}
proc inc{r}{w} = caseL ( m1 => assumeL{w>0}; tick; R.z0 ; assertR{w>0}; delay{r} ; copy{r}{w-1}{w}
                       | z0 => assumeL{w>0}; tick; R.p1 ; assertR{w>0}; delay{r} ; copy{r}{w-1}{w}
                       | p1 => assumeL{w>0}; tick; R.m1 ; assertR{w>0}; delay{r} ; inc{r}{w-1}
                       | e => tick ; R.p1 ; assertR{1>0} ; waitL ; tick; delay{r} ; R.e ; delay ; closeR )

proc dec{r}{w} : ternary{r}{w} |- ()ternary{r}{w+1}
proc dec{r}{w} = caseL ( m1 => assumeL{w>0}; tick; R.p1 ; assertR{w>0}; delay{r} ; dec{r}{w-1}
                       | z0 => assumeL{w>0}; tick; R.m1 ; assertR{w>0}; delay{r} ; copy{r}{w-1}{w}
                       | p1 => assumeL{w>0}; tick; R.z0 ; assertR{w>0}; delay{r} ; copy{r}{w-1}{w}
                       | e => tick; R.m1 ; assertR{1>0} ; waitL ; tick; delay{r}; R.e ; delay ; closeR )

% 2*(3n-1) = 3(2*n)-2 = 3(2*n-1)+1
% 2*(3n+0) = 3(2*n)+0
% 2*(3n+1) = 3(2*n)+2 = 3(2*n+1)-1

(*
proc dbl{r}{w} : ternary{r}{w} |- ()ternary{r+1}{a*w+b}
proc dbl{r}{w} = caseL ( m1 => assumeL{w>0}; tick;      % (r)ternary{r}{w-1} |- ternary{r+1}{a*w+b}
                               R.p1 ; assertR{a*w+b>0}; % (r)ternary{r}{w-1} |- (r+2)ternary{r+1}{a*w+b-1}
                               delay{r} ;               % ternary{r}{w-1} |- (2)ternary{r+1}{a*w+b-1}
                               dbl{r}{w-1} ||           % ternary{r}{w-1} |- ()ternary{r+1}{a*(w-1)+b}
                               (delay ; dec{r+1}{a*(w-1)+b})  % ()ternary{r+1}{a*(w-1)+b} |- (2)ternary{r+1}{a*(w-1)+b+1}
                               % requires: a*w+b-1 = a*(w-1)+b+1 = a*w-a+b+1 = a*w+b-1-a+2
                               % a = 2, b arbitrary (pick b = 0)
                      | z0 => R.z0 ; delay{r} ; dbl{r} || (delay ; copy{r+1})
                      | p1 => R.m1 ; delay{r} ; dbl{r} || (delay ; inc{r+1})
                      | e => R.e ; waitL ; closeR )
*)
proc dbl{r}{w} : ternary{r}{w} |- ()ternary{r+1}{2*w}
proc dbl{r}{w} = caseL ( m1 => assumeL{w>0}; tick;      % (r)ternary{r}{w-1} |- ternary{r+1}{2*w}
                               R.p1 ; assertR{2*w>0};   % (r)ternary{r}{w-1} |- (r+2)ternary{r+1}{2*w-1}
                               delay{r} ;               %    ternary{r}{w-1} |- (2)ternary{r+1}{2*w-1}
                               dbl{r}{w-1} ||           %    ternary{r}{w-1} |- ()ternary{r+1}{2*(w-1)}
                               (delay ; dec{r+1}{2*(w-1)})  % ()ternary{r+1}{2*(w-1)} |- (2)ternary{r+1}{2*(w-1)+1}
                      | z0 => assumeL{w>0}; tick;
                              R.z0 ; assertR{2*w>0};
                              delay{r} ;
                              dbl{r}{w-1} || (delay ; copy{r+1}{2*(w-1)}{2*w-1})
                      | p1 => assumeL{w>0}; tick;
                              R.m1 ; assertR{2*w>0};
                              delay{r} ;
                              dbl{r}{w-1} || (delay ; inc{r+1}{2*(w-1)})
                      | e => tick ; R.e ; waitL ; tick ; closeR )

proc eight{r}{w|w>=3} : ternary{r}{w}
proc eight{r}{w} = R.m1 ; assertR{w>2} ; delay{r+1} ;
                   R.z0 ; assertR{w>1} ; delay{r+1} ;
                   R.p1 ; assertR{w>0} ; delay{r+1} ;
                   R.e ; delay ; closeR

% proc eight = one || dbl || dbl || dbl
proc eight0 : ternary{0}{3}
proc eight0 = eight{0}{3}
exec eight0

% actually, width(19) = 4, but computation requires 9
proc nineteen1 : ({4})ternary{1}{9}
proc nineteen1 = eight0 || dbl{0}{3} [({1})ternary{1}{6}]
                 (delay{1} ; inc{1}{6}) [({2})ternary{1}{7}]
                 (delay{2} ; inc{1}{7}) [({3})ternary{1}{8}]
                 (delay{3} ; inc{1}{8})
exec nineteen1

proc m_eight0 : ()ternary{0}{3}
proc m_eight0 = eight0 || neg{0}{3}
exec m_eight0

type binary{r} = +{ b0 : ({r+1})binary{r},
                    b1 : ({r+1})binary{r},
                    e : ()1 }

proc same{r} : binary{r} |- ()binary{r}
proc succ{r} : binary{r} |- ()binary{r}
proc pred{r} : binary{r} |- ()binary{r}

proc same{r} = caseL ( b0 => tick ; R.b0 ; delay{r} ; same{r}
                     | b1 => tick ; R.b1 ; delay{r}; same{r}
                     | e => tick ; R.e ; waitL ; tick ; closeR )

proc succ{r} = caseL ( b0 => tick ; R.b1 ; delay{r} ; same{r}
                     | b1 => tick ; R.b0 ; delay{r} ; same{r}
                     | e => tick ; R.b1 ; waitL ; tick ; delay{r} ; R.e ; delay ; closeR )

proc pred{r} = caseL ( b0 => tick ; R.b1 ; delay{r} ; pred{r}  % (2n+0)-1 = 2(n-1)+1
                     | b1 => tick ; R.b0 ; delay{r} ; same{r}  % may create leading b0
                     | e => tick ; R.e ; waitL ; tick ; closeR )  % 0-1 = 0, by definition

% 3*(2n+0) = 6*n   = 2(3*n)+0
% 3*(2n+1) = 6*n+3 = 2((3*n)+1)+1
% 3*0 = 0
proc times3{r} : binary{r} |- ()binary{r+1}
proc times3{r} = caseL ( b0 => tick ; R.b0 ; delay{r} ; times3{r} || delay ; same{r+1}
                       | b1 => tick ; R.b1 ; delay{r} ; times3{r} || delay ; succ{r+1}
                       | e => tick ; R.e ; waitL ; tick ; closeR )

proc six0 : binary{0}
proc six0 = R.b0 ; delay ; R.b1 ; delay ; R.b1 ; delay ; R.e ; delay ; closeR

proc eighteen_2 : ()binary{1}
proc eighteen_2 = six0 || times3{0}
exec eighteen_2

% conversion from ternary to binary
% cannot be timed without a bound
% on the width of the input number

(*
proc tern2bin{r}{w} : ternary{r}{w} |- ({a*r+b*w+c})bin{_}
proc tern2bin{r}{w} = caseL ( m1 => assumeL{w>0} ; tick ;  % (r)ternary{r}{w-1} |- (a*r+b*w+c-1)bin{_}
                                    delay{r} ;             % ternary{r}{w-1} |- (a*r+b*w+c-1-r)bin{_}
                                    tern2bin{r}{w-1}       % ternary{r}{w-1} |- (a*r+b*(w-1)+c)bin{_}
                                    || times3              % (a*r+b*(w-1)+c)bin{_} |- (a*r+b(w-1)+c+1)bin{_}
                                    || pred                % (a*r+b*(w-1)+c+1)bin{_} |- (a*r+b(w-1)+c+2)bin{_}
                                    % requires: a*r+b*w+c-1-r = a*r+b*(w-1)+c+2
                                    % (a-1)*r + b*w + c - 1 = a*r + b*w - b + c + 2
                                    % 0 = r - b + 3
                                    % b = r + 3
                      | z0 => tern2bin || times3
                      | p1 => tern2bin || times3 || succ
                      | e => R.e ; <-> )
*)
(*
proc tern2bin{r}{w} : ternary{r}{w} |- ({2*w})bin{_}
proc tern2bin{r}{w} = caseL ( m1 => assumeL{w>0} ; tick ;  % (r)ternary{r}{w-1} |- (2*w-1)bin{a*r+b*w+c}
                                    delay{r} ;             % ternary{r}{w-1} |- (2*w-1-r)bin{a*r+b*w+c}
                                    tern2bin{r}{w-1}       % ternary{r}{w-1} |- (2*(w-1)-1-r)bin{a*r+b*(w-1)+c}
                                    || times3{r}           % (2*(w-1)-1-r)bin{a*r+b*(w-1)+c} |- (2*(w-1)-r)bin{a*r+b*(w-1)+c+1}
                                    || pred{r}             % (2*(w-1)-r)bin{a*r+b*(w-1)+c+1} |- (2*(w-1)-r+1)bin{a*r+b*(w-1)+c+1}
                             % requires: a*r + b*w + c = a*r + b*(w-1) + c + 1
                             % b*w + c = b*w - b + c + 1
                             % b = 1 (choose: a = c = 0)
                      | z0 => tern2bin || times3 || same
                      | p1 => tern2bin || times3 || succ
                      | e => R.e ; <-> )
*)

proc d_times3{d}{r} : ({d})binary{r} |- ({d+1})binary{r+1}
proc d_times3{d}{r} = delay{d} ; times3{r}

proc d_same{d}{r} : ({d})binary{r} |- ({d+1})binary{r}
proc d_pred{d}{r} : ({d})binary{r} |- ({d+1})binary{r}
proc d_succ{d}{r} : ({d})binary{r} |- ({d+1})binary{r}
proc d_same{d}{r} = delay{d} ; same{r}
proc d_pred{d}{r} = delay{d} ; pred{r}
proc d_succ{d}{r} = delay{d} ; succ{r}

proc tern2bin{r}{w} : ternary{r}{w} |- ({(r+3)*w+2})binary{w}
proc tern2bin{r}{w} = caseL ( m1 => assumeL{w>0} ; tick ;  % (r)ternary{r}{w-1} |- ((r+3)*w+1)bin{w}
                                    delay{r} ;             % ternary{r}{w-1} |- ((r+3)*w-r+1)bin{w}
                                    tern2bin{r}{w-1}       % ternary{r}{w-1} |- ((r+3)*(w-1)+2)bin{w-1}
                                    || d_times3{(r+3)*(w-1)+2}{w-1} % ((r+3)*(w-1)+2)bin{w-1} |- ((r+3)*(w-1)+3)bin{w-1}
                                    || d_pred{(r+3)*(w-1)+3}{w} % ((r+3)*(w-1)+3)bin{(w-1)+1} |- ((r+3)*(w-1)+4)bin{(w-1)+1}
                                    % need: (r+3)*w-r+1 =?= (r+3)*(w-1)+4
                      | z0 => assumeL{w>0} ; tick ; delay{r} ;
                              tern2bin{r}{w-1} || d_times3{(r+3)*(w-1)+2}{w-1} || d_same{(r+3)*(w-1)+3}{w}
                      | p1 => assumeL{w>0} ; tick ; delay{r} ;
                              tern2bin{r}{w-1} || d_times3{(r+3)*(w-1)+2}{w-1} || d_succ{(r+3)*(w-1)+3}{w}
                      | e => tick ; waitL ; tick ; delay{(r+3)*w} ; R.e ; tick ; closeR )

proc eight_2 : ({3*3+2})binary{3}
proc eight_2 = eight{0}{3} || tern2bin{0}{3}
exec eight_2

proc nineteen_2 : ({4+4*9+2})binary{9}
proc nineteen_2 = nineteen1 || (delay{4} ; tern2bin{1}{9})
exec nineteen_2

(*
 * Leaving the timing analysis of the remainder
 * to future refinements
 *)

(*
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