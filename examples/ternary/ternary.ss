#options
#test success

type ternary = +{ m1 : ternary,
                  z0 : ternary,
                  p1 : ternary,
                  e : 1 }

proc zero : ternary
proc zero = R.e ; closeR

proc one : ternary
proc one = R.p1 ; R.e ; closeR

proc m_one : ternary
proc m_one = R.m1 ; R.e ; closeR

proc neg : ternary |- ternary
proc neg = caseL ( m1 => R.p1 ; neg
                 | z0 => R.z0 ; neg
                 | p1 => R.m1 ; neg
                 | e => R.e ; <-> )

proc inc : ternary |- ternary
proc inc = caseL ( m1 => R.z0 ; <->
                 | z0 => R.p1 ; <->
                 | p1 => R.m1 ; inc
                 | e => R.p1 ; R.e ; <-> )

proc dec : ternary |- ternary
proc dec = caseL ( m1 => R.p1 ; dec
                 | z0 => R.m1 ; <->
                 | p1 => R.z0 ; <->
                 | e => R.m1 ; R.e ; <-> )

% 2*(3n-1) = 3(2*n)-2 = 3(2*n-1)+1
% 2*(3n+0) = 3(2*n)+0
% 2*(3n+1) = 3(2*n)+2 = 3(2*n+1)-1

proc dbl : ternary |- ternary
proc dbl = caseL ( m1 => R.p1 ; dbl || dec
                 | z0 => R.z0 ; dbl
                 | p1 => R.m1 ; dbl || inc
                 | e => R.e ; <-> )

proc eight : ternary
% proc eight = zero || inc || inc || inc || inc || inc || inc || inc || inc
proc eight = one || dbl || dbl || dbl
exec eight

proc nineteen : ternary
proc nineteen = eight || dbl || inc || inc || inc
exec nineteen

proc m_eight : ternary
proc m_eight = eight || neg
exec m_eight

type binary = +{ b0 : binary,
                 b1 : binary,
                 e : 1 }

proc succ : binary |- binary
proc pred : binary |- binary

proc succ = caseL ( b0 => R.b1 ; <->
                  | b1 => R.b0 ; succ
                  | e => R.b1 ; R.e ; <-> )

proc pred = caseL ( b0 => R.b1 ; pred  % (2n+0)-1 = 2(n-1)+1
                  | b1 => R.b0 ; <->
                  | e => R.e ; <-> )  % 0-1 = 0, by definition

% 3*(2n+0) = 6*n   = 2(3*n)+0
% 3*(2n+1) = 6*n+3 = 2((3*n)+1)+1
% 3*0 = 0
proc times3 : binary |- binary
proc times3 = caseL ( b0 => R.b0 ; times3
                    | b1 => R.b1 ; times3 || succ
                    | e => R.e ; <-> )
proc six : binary
proc six = R.b0 ; R.b1 ; R.b1 ; R.e ; closeR

proc eighteen_2 : binary
proc eighteen_2 = six || times3
exec eighteen_2

% only for positive numbers
proc tern2bin : ternary |- binary
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
