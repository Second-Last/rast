#options --time=recv --syntax=implicit --terminate=equi
#test success

% Binary numbers
% allows leading 0s

type bin{r} = +{b0 : `({r})bin{r}, b1 : `({r})bin{r}, e : `1}

proc zero : bin{1}
proc zero = R.e ; closeR

proc ex0 : bin{1}
proc ex0 = zero
exec ex0

proc copy : bin{1} |- `({0})bin{1} % no additional delay
proc copy = caseL ( b0 => R.b0 ; copy
                  | b1 => R.b1 ; copy
                  | e => R.e ; waitL ; closeR )

proc succ : bin{1} |- `({0})bin{1}
proc succ = caseL ( b0 => R.b1 ; copy % <-> cannot be timed
                  | b1 => R.b0 ; succ
                  | e => R.b1 ; waitL ; R.e ; closeR )
proc ex3 : ({3}) bin{1}
proc ex3 = zero || succ || succ || succ
exec ex3

proc pred : bin{1} |- `({0}) bin{1}
proc pred = caseL ( b0 => R.b1 ; pred
                  | b1 => R.b0 ; copy  % may introduce leading 0!
                  | e => R.e ; waitL ; closeR )  % pred 0 = 0

proc ex2 : ({4}) bin{1}
proc ex2 = ex3 || pred
exec ex2

proc one : ({1}) bin{1}
proc one = zero || succ 

proc ex1 : ({1}) bin{1}
proc ex1 = one
exec ex1

% numbits is not quite log because it counts leading b0s
% cannot be given a fixed temporal type
% also working is:
% proc numbits : bin{1} |- <>bin{1}

proc numbits : bin{1} |- ()<>bin{1}
proc numbits = caseL ( b0 => numbits || succ
                     | b1 => numbits || succ
                     | e => R.e ; waitL ; closeR )

proc ex007 : bin{1}
proc ex007 = R.b1 ; R.b1 ; R.b1 ; R.b0 ; R.b0 ; R.e ; closeR
exec ex007

proc ex5 : ()<>bin{1}
proc ex5 = ex007 || numbits
exec ex5

proc dbl : bin{1} |- ()bin{1}
proc dbl1 : bin{1} |- ()bin{1}

proc dbl = caseL ( b0 => R.b0 ; dbl
                 | b1 => R.b0 ; dbl1
                 | e => R.e ; waitL ; closeR )
proc dbl1 = caseL ( b0 => R.b1 ; dbl
                  | b1 => R.b1 ; dbl1
                  | e => R.b1 ; waitL ; R.e ; closeR )

proc stdize : bin{1} |- ()<>bin{1}
proc stdize = caseL ( b0 => stdize || dbl
                    | b1 => stdize || dbl1
                    | e => R.e ; waitL ; closeR )

% width x = number of bits in the standard form of x (roughly the log)
proc width : bin{1} |- ()<>bin{1}
proc width = stdize || numbits

proc ex3b : <>bin{1}
proc ex3b = ex007 || width
exec ex3b

% sq2 x = x * x for x = 2^y
proc sq2 : bin{1} |- <>bin{1}
proc sq2 = caseL ( b0 => sq2 || dbl || dbl % (2x)^2 = 4(x^2)
                 | b1 => sq2 || dbl1       % (2x+1)^2 = 4(x^2) + 4x + 1, but x = 0
                 | e => R.e ; waitL ; closeR )               % 0^2 = 0

proc ex64 : <>bin{1}
proc ex64 = ex007 || succ || sq2
exec ex64

(* next three are not actually used here *)
proc Rb0 : ()()bin{1} |- bin{1}
proc Rb0 = R.b0 ; <->

proc Rb1 : ()()bin{1} |- bin{1}
proc Rb1 = R.b1 ; <->

proc Re : ()1 |- bin{1}
proc Re = R.e ; <->

% exp x = 2^x
proc exp2 : bin{1} |- <>bin{1}
proc exp2 = caseL ( b0 => exp2 || sq2        % 2^(2x) = (2^x)^2
                  | b1 => exp2 || sq2 || dbl % 2^(2x+1) = 2*2^(2x)
                  | e =>  R.b1 ; waitL ; R.e ; closeR )

proc ex32 : <>bin{1}
proc ex32 = ex5 || exp2
exec ex32

% some predicates
% bbool outputs a boolean followed by a binary number
type bbool{r} = +{false : ()bin{r}, true : ()bin{r}}

proc copy2 : bin{1} |- ()()bin{1}
proc copy2 = copy || copy

proc is_even : bin{1} |- ()bbool{1}
proc is_even =
     caseL ( b0 =>     % ()bin |- bool
             R.true ;  % ()bin |- ()bin
             R.b0 ;    % bin |- ()()bin
             copy2
           | b1 => R.false ; R.b1 ; copy2
           | e => R.true ; waitL ; R.e ; closeR )

proc not : bbool{1} |- ()bbool{1}
proc not =
     caseL ( false => R.true ; copy
           | true => R.false ; copy )

proc exf32 : ()()<>bbool{1}
proc exf32 = ex32 || is_even || not
exec exf32

% is_zero also standardizes 0, but not positive numbers
proc is_zero : bin{1} |- <>bbool{1}
proc is_zero =
     caseL ( b0 =>                     % ()bin |- <>bool
                   is_zero ||          % <>bool |- <>bool
                   caseL ( false =>    % bin |- <>bool
                           R.false ;   % bin |- ()bin
                           dbl
                         | true =>     % bin |- <>bool
                           R.true ;    % bin |- ()bin
                           copy )
           | b1 =>                     % ()bin |- <>bool
                   R.false ;           % ()bin |- ()bin
                   R.b1 ;              %   bin |- ()()bin
                   copy2
           | e  =>                     %     1 |- <>bool
                   R.true ;            %     1 |- ()bin
                   waitL ;             %     . |- bin
                   R.e ;               %     . |- ()1
                   closeR )

proc ext32 : <>bbool{1}
proc ext32 = ex32 || is_zero || not
exec ext32

proc ext0 : <>bbool{1}
proc ext0 = (R.b0 ; R.b0 ; R.e ; closeR) [bin{1}] is_zero
exec ext0


type tet{s} = +{b0 : `({s})tet{s}, b1 : `({s})tet{s}, b2 : `({s})tet{s}, b3 : `({s})tet{s}, e : `1}

proc copy_tet : tet{3} |- ()tet{3}
proc copy_tet = caseL ( b0 => R.b0 ; copy_tet
                      | b1 => R.b1 ; copy_tet
                      | b2 => R.b2 ; copy_tet
                      | b3 => R.b3 ; copy_tet
                      | e => R.e ; waitL ; closeR )

proc bin2tet : bin{1} |- ({4})tet{3}                    %   bin |- (k) tet{s}
proc bin2tet =
     caseL ( b0 =>                                      % ()bin |- (k-1) tet{s}
                   caseL ( b0 =>                        % ()bin |- (k-3) tet{s}  , k-3 = 1 so k = 4
                                 R.b0 ;                 %   bin |- ()(s) tet{s}  , s+1 = k so s = 3
                                 bin2tet
                         | b1 => R.b2 ; bin2tet
                         | e => waitL ; R.e ; closeR )
           | b1 => caseL ( b0 => R.b1 ; bin2tet
                         | b1 => R.b3 ; bin2tet
                         | e => waitL ; R.b1 ; R.e ; closeR )
           | e => waitL ; R.e ; closeR )

proc ex7t : ({4})tet{3}
proc ex7t = ex007 || bin2tet
exec ex7t  % (7)_10 = (111)_2 = (13)_4

proc succ_tet : tet{3} |- ()tet{3}
proc succ_tet =
     caseL ( b0 => R.b1 ; copy_tet
           | b1 => R.b2 ; copy_tet
           | b2 => R.b3 ; copy_tet
           | b3 => R.b0 ; succ_tet
           | e  => R.b1 ; waitL ; R.e ; closeR )

(* cannot type this as given without <>, because of the trailing
 * call to succ_tet where there is a carry
 * use two versions, one with and one without curry
 *)
(*
proc checksum : tet{3} |- ({k})tet{s}
proc checksum =
     caseL ( b0 =>                                   % (3)tet{3} |- (k-1)tet{s}
                                                     %    tet{3} |- (k-4)tet{s}
                   caseL ( b0 =>                     % (3)tet{3} |- (k-5)tet{s}
                                                     %    tet{3} |- (k-8)tet{s}   k-8 = 0
                                 R.b0 ;              %    tet{3} |- ()(s)tet{s}   s+1 = k
                                 checksum ||         %    tet{3} |- (k)tet{s} || (k)tet{s} |- (k+1)tet{s}
                                 copy_tet
                         | b1 => R.b1 ; checksum || copy_tet
                         | b2 => R.b2 ; checksum || copy_tet
                         | b3 => R.b3 ; checksum || copy_tet
                         | e  => R.b0 ; waitL ; R.e ; closeR )
           | b1 => caseL ( b0 => R.b1 ; checksum || copy_tet
                         | b1 => R.b2 ; checksum || copy_tet
                         | b2 => R.b3 ; checksum || copy_tet
                         | b3 => R.b0 ; checksum || succ_tet
                         | e  => R.b1 ; waitL ; R.e ; closeR )
           | b2 => caseL ( b0 => R.b2 ; checksum || copy_tet
                         | b1 => R.b3 ; checksum || copy_tet
                         | b2 => R.b0 ; checksum || succ_tet
                         | b3 => R.b1 ; checksum || succ_tet
                         | e  => R.b2 ; waitL ; R.e ; closeR )
           | b3 => caseL ( b0 => R.b3 ; checksum || copy_tet
                         | b1 => R.b0 ; checksum || succ_tet
                         | b2 => R.b1 ; checksum || succ_tet
                         | b3 => R.b2 ; checksum || succ_tet
                         | e  => R.b3 ; waitL ; R.e ; closeR )
           | e  => R.e ; waitL ; closeR )

*)

proc checksum : tet{3} |- ({8})tet{7}
proc checksum_c : tet{3} |- ({8})tet{7}
proc checksum =
     caseL ( b0 =>                                   % (3)tet{3} |- (k-1)tet{s}
                                                     %    tet{3} |- (k-4)tet{s}
                   caseL ( b0 =>                     % (3)tet{3} |- (k-5)tet{s}
                                                     %    tet{3} |- (k-8)tet{s}   k-8 = 0
                                 R.b0 ;              %    tet{3} |- ()(s)tet{s}   s+1 = k
                                 checksum            %    tet{3} |- (k)tet{s}
                         | b1 => R.b1 ; checksum
                         | b2 => R.b2 ; checksum
                         | b3 => R.b3 ; checksum
                         | e  => waitL ; R.b0 ; R.e ; closeR )
           | b1 => caseL ( b0 => R.b1 ; checksum
                         | b1 => R.b2 ; checksum
                         | b2 => R.b3 ; checksum
                         | b3 => R.b0 ; checksum_c
                         | e  => waitL ; R.b1 ; R.e ; closeR )
           | b2 => caseL ( b0 => R.b2 ; checksum
                         | b1 => R.b3 ; checksum
                         | b2 => R.b0 ; checksum_c
                         | b3 => R.b1 ; checksum_c
                         | e  => waitL ; R.b2 ; R.e ; closeR )
           | b3 => caseL ( b0 => R.b3 ; checksum
                         | b1 => R.b0 ; checksum_c
                         | b2 => R.b1 ; checksum_c
                         | b3 => R.b2 ; checksum_c
                         | e  => waitL ; R.b3 ; R.e ; closeR )
           | e  => waitL ; R.e ; closeR )

proc checksum_c =
     caseL ( b0 => caseL ( b0 => R.b1 ; checksum
                         | b1 => R.b2 ; checksum
                         | b2 => R.b3 ; checksum
                         | b3 => R.b0 ; checksum_c
                         | e  => waitL ; R.b1 ; R.e ; closeR )
           | b1 => caseL ( b0 => R.b2 ; checksum
                         | b1 => R.b3 ; checksum
                         | b2 => R.b0 ; checksum_c
                         | b3 => R.b1 ; checksum_c
                         | e  => waitL ; R.b2 ; R.e ; closeR )
           | b2 => caseL ( b0 => R.b3 ; checksum
                         | b1 => R.b0 ; checksum_c
                         | b2 => R.b1 ; checksum_c
                         | b3 => R.b2 ; checksum_c
                         | e  => waitL ; R.b3 ; R.e ; closeR )
           | b3 => caseL ( b0 => R.b0 ; checksum_c
                         | b1 => R.b1 ; checksum_c
                         | b2 => R.b2 ; checksum_c
                         | b3 => R.b3 ; checksum_c
                         | e  => waitL ; R.b0 ; R.b1; R.e ; closeR )
           | e  => waitL ; R.b1 ; R.e ; closeR )


proc ex4t : ({12})tet{7}
proc ex4t = ex7t || checksum
exec ex4t   % sum (7)_10 = sum (31)_4 = (10)_4

proc t4p0 : tet{7} |- ()tet{7}
proc t4p1 : tet{7} |- ()tet{7}
proc t4p2 : tet{7} |- ()tet{7}
proc t4p3 : tet{7} |- ()tet{7}
proc t4p0 = caseL ( b0 => R.b0 ; t4p0
                  | b1 => R.b0 ; t4p1
                  | b2 => R.b0 ; t4p2
                  | b3 => R.b0 ; t4p3
                  | e  => R.e ; waitL ; closeR ) % omit R.b0 (leading 0)
proc t4p1 = caseL ( b0 => R.b1 ; t4p0
                  | b1 => R.b1 ; t4p1
                  | b2 => R.b1 ; t4p2
                  | b3 => R.b1 ; t4p3
                  | e  => R.b1 ; waitL ; R.e ; closeR )
proc t4p2 = caseL ( b0 => R.b2 ; t4p0
                  | b1 => R.b2 ; t4p1
                  | b2 => R.b2 ; t4p2
                  | b3 => R.b2 ; t4p3
                  | e  => R.b2 ; waitL ; R.e ; closeR )
proc t4p3 = caseL ( b0 => R.b3 ; t4p0
                  | b1 => R.b3 ; t4p1
                  | b2 => R.b3 ; t4p2
                  | b3 => R.b3 ; t4p3
                  | e  => R.b3 ; waitL ; R.e ; closeR )

proc is_tet_digit : tet{7} |- ({16})+{false : ()()tet{7}, true : ()()tet{7}}
proc is_tet_digit =               % tet{7} |- (k)bool
     caseL ( b0 =>                % (7)tet{7} |- (k-1)bool
                                  % tet{7} |- (k-8)bool
                   caseL ( b0 =>  % (7)tet{7} |- (k-9)bool
                                  % tet{7}    |- (k-16)bool   k-16 = 0
                           R.false ; % tet{7} |- ()()tet{7}
                           t4p0 || t4p0
                         | b1 => R.false ; t4p1 || t4p0
                         | b2 => R.false ; t4p2 || t4p0
                         | b3 => R.false ; t4p3 || t4p0
                         | e  => waitL ; R.true ; R.e ; closeR ) % drop leading 0
           | b1 => caseL ( b0 => R.false ; t4p0 || t4p1
                         | b1 => R.false ; t4p1 || t4p1
                         | b2 => R.false ; t4p2 || t4p1
                         | b3 => R.false ; t4p3 || t4p1
                         | e  => waitL ; R.true ; R.b1 ; R.e ; closeR )
           | b2 => caseL ( b0 => R.false ; t4p0 || t4p2
                         | b1 => R.false ; t4p1 || t4p2
                         | b2 => R.false ; t4p2 || t4p2
                         | b3 => R.false ; t4p3 || t4p2
                         | e  => waitL ; R.true ; R.b2 ; R.e ; closeR )
           | b3 => caseL ( b0 => R.false ; t4p0 || t4p3
                         | b1 => R.false ; t4p1 || t4p3
                         | b2 => R.false ; t4p2 || t4p3
                         | b3 => R.false ; t4p3 || t4p3
                         | e  => waitL ; R.true ; R.b3 ; R.e ; closeR )
           | e  => waitL ; R.true ; R.e ; closeR )

proc consume_tet : tet{7} |- <>1
proc consume_tet =
     caseL ( b0 => consume_tet
           | b1 => consume_tet
           | b2 => consume_tet
           | b3 => consume_tet
           | e  => waitL ; closeR )

type bool = +{false : <>1, true : <>1}

(* postponing the remainder of divisibility test *)

(* problem here: tet{3} |- checksum : (..)tet{7}, so
 * the recursive call to is_div3 fails since tet{3} <> tet{7}
 * roughly, it should look something like what is below: the
 * interval between successive recursive calls is getting
 * larger.  One could probable define a version of tet
 * with a diamond type upon recursion, obscuring the level
 * of detail, but then supporting functions would also have to
 * be rewritted with this new imprecise type
 *)
(* see bin-time-param.ss *)
(*
type tet{s} = +{b0 : ({s+1})tet{s}, b1 : ({s+1})tet{s}, b2 : ({s+1})tet{s}, b3 : ({s+1})tet{s}, e : `1}
type bool = +{false : <>1, true : <>1}
%
proc checksum{r}     : tet{r} |- ({2*(r+1)}) tet{2*r+1}
proc is_tet_digit{s} : tet{s} |- ({2*(s+1)})+{false : ()()tet{s}, true : ()()tet{s}}
proc consume_tet{t}  : tet{t} |- <>1
%
proc is_div3{r} : tet{r} |- <>bool
proc is_div3{r} = checksum{r} || is_tet_digit{2*r+1}
               || caseL ( false => is_div3{2*r+1}
                        | true => caseL ( b0 => R.false ; consume_tet{2*r+1}
                                        | b1 => R.false ; consume_tet{2*r+1}
                                        | b2 => R.false ; consume_tet{2*r+1}
                                        | b3 => R.true  ; consume_tet{2*r+1}
                                        | e  => waitL ; R.true ; closeR ) )

proc ex7div3 : <>bool
proc ex7div3 = (R.b1 ; R.b1 ; R.b1 ; R.e ; closeR) [bin] bin2tet || is_div3
exec ex7div3  % false

proc ex8div3 : <>bool
proc ex8div3 = (R.b1 ; R.b0 ; R.b0 ; R.b0 ; R.e ; closeR) [bin] bin2tet || is_div3
exec ex8div3  % false

proc ex9div3 : <>bool
proc ex9div3 = (R.b1 ; R.b0 ; R.b0 ; R.b1 ; R.e ; closeR) [bin] bin2tet || is_div3
exec ex9div3  % true

proc ex10div3 : <>bool
proc ex10div3 = (R.b1 ; R.b0 ; R.b1 ; R.b0 ; R.e ; closeR) [bin] bin2tet || is_div3
exec ex10div3  % false
*)

% decimal numbers
type dec{r} = +{b0 : ({r+1})dec{r}, b1 : ({r+1})dec{r}, b2 : ({r+1})dec{r}, b3 : ({r+1})dec{r},
                b4 : ({r+1})dec{r}, b5 : ({r+1})dec{r}, b6 : ({r+1})dec{r}, b7 : ({r+1})dec{r},
                b8 : ({r+1})dec{r}, b9 : ({r+1})dec{r}, e : ()1}

proc zero_dec : dec{1}
proc zero_dec = R.e ; closeR

proc copy_dec : dec{1} |- ()dec{1}
proc copy_dec =
     caseL ( b0 => R.b0 ; copy_dec
           | b1 => R.b1 ; copy_dec  
           | b2 => R.b2 ; copy_dec   
           | b3 => R.b3 ; copy_dec
           | b4 => R.b4 ; copy_dec
           | b5 => R.b5 ; copy_dec
           | b6 => R.b6 ; copy_dec  
           | b7 => R.b7 ; copy_dec       
           | b8 => R.b8 ; copy_dec       
           | b9 => R.b9 ; copy_dec
           | e  => R.e ; waitL ; closeR )

proc succ_dec : dec{1} |- ()dec{1}
proc succ_dec =
     caseL ( b0 => R.b1 ; copy_dec
           | b1 => R.b2 ; copy_dec  
           | b2 => R.b3 ; copy_dec   
           | b3 => R.b4 ; copy_dec
           | b4 => R.b5 ; copy_dec
           | b5 => R.b6 ; copy_dec
           | b6 => R.b7 ; copy_dec  
           | b7 => R.b8 ; copy_dec       
           | b8 => R.b9 ; copy_dec       
           | b9 => R.b0 ; succ_dec
           | e  => R.b1 ; waitL ; R.e ; closeR )

proc dbl_dec : dec{1} |- ()dec{1}
proc dbl_dec1 : dec{1} |- ()dec{1}

proc dbl_dec =
     caseL ( b0 => R.b0 ; dbl_dec  % 2*(10x+0) = 10*(2x)+0
           | b1 => R.b2 ; dbl_dec  % 2*(10x+1) = 10*(2x)+2
           | b2 => R.b4 ; dbl_dec
           | b3 => R.b6 ; dbl_dec
           | b4 => R.b8 ; dbl_dec
           | b5 => R.b0 ; dbl_dec1
           | b6 => R.b2 ; dbl_dec1
           | b7 => R.b4 ; dbl_dec1  % 2*(10x+7) = 20x+14 = 10*(2x+1)+4
           | b8 => R.b6 ; dbl_dec1
           | b9 => R.b8 ; dbl_dec1
           | e  => R.e ; waitL ; closeR ) % 2*0 = 0
proc dbl_dec1 =
     caseL ( b0 => R.b1 ; dbl_dec   % 2*(10x+0)+1 = 10*(2x)+1
           | b1 => R.b3 ; dbl_dec
           | b2 => R.b5 ; dbl_dec
           | b3 => R.b7 ; dbl_dec
           | b4 => R.b9 ; dbl_dec
           | b5 => R.b1 ; dbl_dec1
           | b6 => R.b3 ; dbl_dec1  % 2*(10x+6)+1 = 20x+13 = 10*(2x+1)+3
           | b7 => R.b5 ; dbl_dec1
           | b8 => R.b7 ; dbl_dec1
           | b9 => R.b9 ; dbl_dec1
           | e  => R.b1 ; waitL ; R.e ; closeR ) % 2*0+1 = 1

proc ext364d : ()dec{1}
proc ext364d = (R.b2 ; R.b8 ; R.b1 ; R.e ; closeR) [dec{1}] dbl_dec
exec ext364d

% give up on precise characterization, as in bin2tet
proc bin2dec : bin{1} |- <>dec{1}
proc bin2dec =
     caseL ( b0 => bin2dec || dbl_dec
           | b1 => bin2dec || dbl_dec || succ_dec
           | e => R.e ; waitL ; closeR )

proc ex64d : <>dec{1}
proc ex64d = ex64 || bin2dec
exec ex64d

proc ex7d : <>dec{1}
proc ex7d = ex007 || bin2dec
exec ex7d

proc times10 : bin{1} |- <>bin{1}
proc times10 =
     caseL ( b0 => times10 || dbl           % 10 * (2x) = 2(10 * x)
           | b1 => times10 || dbl || succ   % 10 * (2x+1) = 2(10 * x) + 10
                   || succ || succ || succ
                   || succ || succ || succ
                   || succ || succ || succ
          | e => R.e ; waitL ; closeR       % 10 * 0 = 0
          )

proc dec2bin : dec{1} |- <>bin{1}
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
           | e  => R.e ; waitL ; closeR )

proc ex217d : dec{1}
proc ex217d = R.b7 ; R.b1 ; R.b2 ; R.e ; closeR
exec ex217d

proc ex217 : <>bin{1}
proc ex217 = ex217d || dec2bin
exec ex217

proc ex217d' : <>dec{1}
proc ex217d' = ex217 || bin2dec
exec ex217d'

(* Not sure how to temporally annotate the counter in this form *)
(* For another form, see icfp18/sec3i.ss *)

(*
type ctr = &{ inc : ctr,
              val : bin }

proc counter : bin |- ctr
proc counter =
     caseR ( inc => succ || counter
           | val => <-> )

proc ex221 : dec
proc ex221 = ex217 || counter || (L.inc ; L.inc ; L.inc ; L.inc ; L.val ; <->) [bin] bin2dec
exec ex221
*)
