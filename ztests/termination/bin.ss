#options --terminate=equi
#test success

% Binary numbers
% allows leading 0s

type bin = +{b0 : bin, b1 : bin, e : 1}

proc Rb0 : bin |- bin
proc Rb1 : bin |- bin
proc Re : 1 |- bin
proc Rb0 = R.b0 ; <->
proc Rb1 = R.b1 ; <->
proc Re = R.e ; <->

proc zero : bin
proc zero = R.e ; closeR

proc ex0 : bin
proc ex0 = zero
exec ex0

proc copy : bin |- bin
proc copy = caseL ( b0 => R.b0 ; copy
                  | b1 => R.b1 ; copy
                  | e => R.e ; waitL ; closeR )

proc succ : bin |- bin
proc succ = caseL ( b0 => R.b1 ; <->
                  | b1 => R.b0 ; succ
                  | e => R.b1 ; waitL ; R.e ; closeR )
proc ex3 : bin
proc ex3 = zero || succ || succ || succ
exec ex3

proc pred : bin |- bin
proc pred = caseL ( b0 => R.b1 ; pred
                  | b1 => R.b0 ; <->  % may introduce leading 0!
                  | e => R.e ; <-> )  % pred 0 = 0

proc ex2 : bin
proc ex2 = ex3 || pred
exec ex2

proc one : bin
proc one = zero || succ 

proc ex1 : bin
proc ex1 = one
exec ex1

% numbits is not quite log because it counts leading b0s
proc numbits : bin |- bin
proc numbits = caseL ( b0 => numbits || succ
                     | b1 => numbits || succ
                     | e => Re )

proc ex007 : bin
proc ex007 = R.b1 ; R.b1 ; R.b1 ; R.b0 ; R.b0 ; R.e ; closeR
exec ex007

proc ex5 : bin
proc ex5 = ex007 || numbits
exec ex5

proc dbl : bin |- bin           % y = 2x, y standard
proc dbl1 : bin |- bin          % y = 2x+1, y standard
proc dbl = caseL ( b0 => dbl  || Rb0
                 | b1 => dbl1 || Rb0
                 | e  => Re )
proc dbl1 = caseL ( b0 => dbl  || Rb1
                  | b1 => dbl1 || Rb1
                  | e  => Re   || Rb1 )

proc stdize : bin |- bin
proc stdize = caseL ( b0 => dbl
                    | b1 => dbl1
                    | e => Re )

% width x = number of bits in the standard form of x (roughly the log)
proc width : bin |- bin
proc width = stdize || numbits

proc ex3b : bin
proc ex3b = ex007 || width

% sq2 x = x * x for x = 2^y
proc sq2 : bin |- bin
proc sq2 = caseL ( b0 => sq2 || dbl || dbl % (2x)^2 = 4x^2
                 | b1 => sq2 || dbl1       % (2x+1)^2 = 4x^2 + 4x + 1, but x = 0!
                 | e => Re )               % 0^2 = 0

proc ex64 : bin
proc ex64 = ex007 || succ || sq2
exec ex64

% exp x = 2^x
proc exp2 : bin |- bin
proc exp2 = caseL ( b0 => exp2 || sq2        % 2^(2x) = (2^x)^2
                  | b1 => exp2 || sq2 || dbl % 2^(2x+1) = 2*2^(2x)
                  | e =>  Re || Rb1 )

proc ex32 : bin
proc ex32 = ex5 || exp2
exec ex32

% some predicates
% bbool outputs a boolean followed by a binary number
type bbool = +{false : bin, true : bin}

proc is_even : bin |- bbool
proc is_even =
     caseL ( b0 => R.true ; R.b0 ; <->
           | b1 => R.false ; R.b1 ; <->
           | e => R.true ; R.e ; <-> )

proc not : bbool |- bbool
proc not =
     caseL ( false => R.true ; <->
           | true => R.false ; <-> )

proc exf32 : bbool
proc exf32 = ex32 || is_even || not
exec exf32

% is_zero also standardizes 0, but not positive numbers
proc is_zero : bin |- bbool
proc is_zero =
     caseL ( b0 => is_zero ||
                   caseL ( false => R.false ; R.b0 ; <->
                         | true => R.true ; <-> )
           | b1 => R.false ; R.b1 ; <->
           | e  => R.true ; R.e ; <-> )

proc ext32 : bbool
proc ext32 = ex32 || is_zero || not
exec ext32

proc ext0 : bbool
proc ext0 = (R.b0 ; R.b0 ; R.e ; closeR) [bin] is_zero
exec ext0

type tet = +{b0 : tet, b1 : tet, b2 : tet, b3 : tet, e : 1}
proc bin2tet : bin |- tet
proc bin2tet =
     caseL ( b0 => caseL ( b0 => R.b0 ; bin2tet
                         | b1 => R.b2 ; bin2tet
                         | e => R.e ; <-> )
           | b1 => caseL ( b0 => R.b1 ; bin2tet
                         | b1 => R.b3 ; bin2tet
                         | e => R.b1 ; R.e ; <->)
           | e => R.e ; <-> )

proc ex7t : tet
proc ex7t = ex007 || bin2tet
exec ex7t  % (7)_10 = (111)_2 = (13)_4

proc succ_tet : tet |- tet
proc succ_tet =
     caseL ( b0 => R.b1 ; <->
           | b1 => R.b2 ; <->
           | b2 => R.b3 ; <->
           | b3 => R.b0 ; succ_tet
           | e  => R.b1 ; R.e ; <-> )

proc checksum : tet |- tet
proc checksum =
     caseL ( b0 => caseL ( b0 => R.b0 ; checksum
                         | b1 => R.b1 ; checksum
                         | b2 => R.b2 ; checksum
                         | b3 => R.b3 ; checksum
                         | e  => R.b0 ; R.e ; <-> )
           | b1 => caseL ( b0 => R.b1 ; checksum
                         | b1 => R.b2 ; checksum
                         | b2 => R.b3 ; checksum
                         | b3 => R.b0 ; checksum || succ_tet
                         | e  => R.b1 ; R.e ; <-> )
           | b2 => caseL ( b0 => R.b2 ; checksum
                         | b1 => R.b3 ; checksum
                         | b2 => R.b0 ; checksum || succ_tet
                         | b3 => R.b1 ; checksum || succ_tet
                         | e  => R.b2 ; R.e ; <-> )
           | b3 => caseL ( b0 => R.b3 ; checksum
                         | b1 => R.b0 ; checksum || succ_tet
                         | b2 => R.b1 ; checksum || succ_tet
                         | b3 => R.b2 ; checksum || succ_tet
                         | e  => R.b3 ; R.e ; <-> )
           | e  => R.e ; <-> )

proc ex4t : tet
proc ex4t = ex7t || checksum
exec ex4t   % sum (7)_10 = sum (31)_4 = (10)_4

proc is_tet_digit : tet |- +{false : tet, true : tet}
proc is_tet_digit =
     caseL ( b0 => caseL ( b0 => R.false ; R.b0 ; R.b0 ; <->
                         | b1 => R.false ; R.b0 ; R.b1 ; <->
                         | b2 => R.false ; R.b0 ; R.b2 ; <->
                         | b3 => R.false ; R.b0 ; R.b3 ; <->
                         | e  => R.true  ; R.b0 ; R.e ; <-> )
           | b1 => caseL ( b0 => R.false ; R.b1 ; R.b0 ; <->
                         | b1 => R.false ; R.b1 ; R.b1 ; <->
                         | b2 => R.false ; R.b1 ; R.b2 ; <->
                         | b3 => R.false ; R.b1 ; R.b3 ; <->
                         | e  => R.true  ; R.b1 ; R.e ; <-> )    
           | b2 => caseL ( b0 => R.false ; R.b2 ; R.b0 ; <->
                         | b1 => R.false ; R.b2 ; R.b1 ; <->
                         | b2 => R.false ; R.b2 ; R.b2 ; <->
                         | b3 => R.false ; R.b2 ; R.b3 ; <->
                         | e  => R.true  ; R.b2 ; R.e ; <-> )    
           | b3 => caseL ( b0 => R.false ; R.b3 ; R.b0 ; <->
                         | b1 => R.false ; R.b3 ; R.b1 ; <->
                         | b2 => R.false ; R.b3 ; R.b2 ; <->
                         | b3 => R.false ; R.b3 ; R.b3 ; <->
                         | e  => R.true  ; R.b3 ; R.e ; <-> )
           | e  => R.true ; R.e ; <-> )

proc consume_tet : tet |- 1
proc consume_tet =
     caseL ( b0 => consume_tet
           | b1 => consume_tet
           | b2 => consume_tet
           | b3 => consume_tet
           | e  => <-> )

type bool = +{false : 1, true : 1}

% the termination checker currently cannot verify
% termination for is_div3
proc is_div3 : tet |- bool
proc is_div3 = checksum || is_tet_digit
               || caseL ( false => is_div3
                        | true => caseL ( b0 => R.false ; consume_tet
                                        | b1 => R.false ; consume_tet
                                        | b2 => R.false ; consume_tet
                                        | b3 => R.true  ; consume_tet
                                        | e  => R.true ; <-> ) )

proc ex7div3 : bool
proc ex7div3 = (R.b1 ; R.b1 ; R.b1 ; R.e ; closeR) [bin] bin2tet || is_div3
exec ex7div3  % false

proc ex8div3 : bool
proc ex8div3 = (R.b1 ; R.b0 ; R.b0 ; R.b0 ; R.e ; closeR) [bin] bin2tet || is_div3
exec ex8div3  % false

proc ex9div3 : bool
proc ex9div3 = (R.b1 ; R.b0 ; R.b0 ; R.b1 ; R.e ; closeR) [bin] bin2tet || is_div3
exec ex9div3  % true

proc ex10div3 : bool
proc ex10div3 = (R.b1 ; R.b0 ; R.b1 ; R.b0 ; R.e ; closeR) [bin] bin2tet || is_div3
exec ex10div3  % false

% decimal numbers
type dec = +{b0 : dec, b1 : dec, b2 : dec, b3 : dec, b4 : dec,
             b5 : dec, b6 : dec, b7 : dec, b8 : dec, b9 : dec,
             e : 1}

proc zero_dec : dec
proc zero_dec = R.e ; closeR

proc succ_dec : dec |- dec
proc succ_dec =
     caseL ( b0 => R.b1 ; <->
           | b1 => R.b2 ; <->       
           | b2 => R.b3 ; <->       
           | b3 => R.b4 ; <->       
           | b4 => R.b5 ; <->       
           | b5 => R.b6 ; <->       
           | b6 => R.b7 ; <->       
           | b7 => R.b8 ; <->       
           | b8 => R.b9 ; <->       
           | b9 => R.b0 ; succ_dec
           | e => R.b1 ; R.e ; <-> )

proc dbl_dec : dec |- dec
proc dbl_dec =
     caseL ( b0 => R.b0 ; dbl_dec
           | b1 => R.b2 ; dbl_dec
           | b2 => R.b4 ; dbl_dec
           | b3 => R.b6 ; dbl_dec
           | b4 => R.b8 ; dbl_dec
           | b5 => R.b0 ; dbl_dec || succ_dec
           | b6 => R.b2 ; dbl_dec || succ_dec
           | b7 => R.b4 ; dbl_dec || succ_dec
           | b8 => R.b6 ; dbl_dec || succ_dec
           | b9 => R.b8 ; dbl_dec || succ_dec
           | e  => R.e ; <-> )

proc bin2dec : bin |- dec
proc bin2dec =
     caseL ( b0 => bin2dec || dbl_dec
           | b1 => bin2dec || dbl_dec || succ_dec
           | e => R.e ; <-> )

proc ex64d : dec
proc ex64d = ex64 || bin2dec
exec ex64d

proc ex7d : dec
proc ex7d = ex007 || bin2dec
exec ex7d

proc times10 : bin |- bin
proc times10 =
     caseL ( b0 => times10 || dbl           % 10 * (2x) = 2(10 * x)
           | b1 => times10 || dbl || succ   % 10 * (2x+1) = 2(10 * x) + 10
                   || succ || succ || succ
                   || succ || succ || succ
                   || succ || succ || succ
          | e => R.e ; <->                  % 10 * 0 = 0
          )

proc dec2bin : dec |- bin
proc dec2bin =
     caseL ( b0 => dec2bin || times10
           | b1 => dec2bin || times10 || succ
           | b2 => dec2bin || times10 || succ || succ
           | b3 => dec2bin || times10 || succ || succ || succ
           | b4 => dec2bin || times10 || succ || succ || succ || succ
           | b5 => dec2bin || times10 || succ || succ || succ || succ || succ
           | b6 => dec2bin || times10 || succ || succ || succ || succ || succ || succ
           | b7 => dec2bin || times10 || succ || succ || succ || succ || succ || succ || succ
           | b8 => dec2bin || times10 || succ || succ || succ || succ || succ || succ || succ || succ
           | b9 => dec2bin || times10 || succ || succ || succ || succ || succ || succ || succ || succ || succ
           | e  => R.e ; <-> )

proc ex217d : dec
proc ex217d = R.b7 ; R.b1 ; R.b2 ; R.e ; closeR
exec ex217d

proc ex217 : bin
proc ex217 = ex217d || dec2bin
exec ex217

proc ex217d' : dec
proc ex217d' = ex217 || bin2dec
exec ex217d'

type ctr = &{ inc : ctr,
              val : bin }

proc counter : bin |- ctr
proc counter =
     caseR ( inc => succ || counter
           | val => <-> )

proc ex221 : dec
proc ex221 = ex217 || counter || (L.inc ; L.inc ; L.inc ; L.inc ; L.val ; <->) [bin] bin2dec
exec ex221
