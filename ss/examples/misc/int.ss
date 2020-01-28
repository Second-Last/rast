(* Binary integers using positive and negative digits *)

type int = +{d0 : int, p1 : int, m1 : int, e : 1}

proc zero : int
proc zero = R.e ; closeR

proc succ : int |- int
proc succ = caseL ( d0 => R.p1 ; <->
                  | p1 => R.d0 ; succ
                  | m1 => R.d0 ; <->
                  | e  => R.p1 ; R.e ; waitL ; closeR )

proc pred : int |- int
proc pred = caseL ( d0 => R.m1 ; <->
                  | p1 => R.d0 ; <->
                  | m1 => R.d0 ; pred
                  | e  => R.m1 ; R.e ; waitL ; closeR )

proc neg : int |- int
proc neg = caseL ( d0 => R.d0 ; neg
                 | p1 => R.m1 ; neg
                 | m1 => R.p1 ; neg
                 | e =>  R.e ; waitL ; closeR )

(********************)
(* Testing the sign *)
(********************)

(* sign is the sign of the highest bit *)

type sign = +{zero : 1, pos : 1, neg : 1}

(* these processes consume the integer *)
proc neu2sign : int |- sign
proc pos2sign : int |- sign
proc neg2sign : int |- sign

proc neu2sign = caseL ( d0 => neu2sign
                      | p1 => pos2sign
                      | m1 => neg2sign
                      | e => R.zero ; waitL ; closeR )

proc pos2sign = caseL ( d0 => pos2sign
                      | p1 => pos2sign
                      | m1 => neg2sign
                      | e => R.pos ; waitL ; closeR )

proc neg2sign = caseL ( d0 => neg2sign
                      | p1 => pos2sign
                      | m1 => neg2sign
                      | e => R.neg ; waitL ; closeR )

(* this processes produces the sign, followed by the original integer *)
type sign_test = +{zero : int, pos : int, neg : int}

proc sgn_test : int |- sign_test
proc sgn_test = caseL ( d0 => sgn_test || caseL ( zero => R.zero ; R.d0 ; <->
                                                | pos  => R.pos ; R.d0 ; <->
                                                | neg  => R.neg ; R.d0 ; <-> )
                      | p1 => sgn_test || caseL ( zero => R.pos ; R.p1 ; <->
                                                | pos  => R.pos ; R.p1 ; <->
                                                | neg  => R.neg ; R.p1 ; <-> )
                      | m1 => sgn_test || caseL ( zero => R.neg ; R.m1 ; <->
                                                | pos  => R.pos ; R.m1 ; <->
                                                | neg  => R.neg ; R.m1 ; <-> )  
                      | e => R.zero ; R.e ; <-> )


(*
 * Standard forms
 * no leading zeros
 * all digits are positive or all digits are negative
 *
 * type zero = +{e : 1}
 * type neg_or_zero = +{d0 : neg, m1 : neg_or_zero, e : 1}
 * type neg = +{d0 : neg, m1 : neg_or_zero}
 * type pos = +{d0 : pos, p1 : pos_or_zero}
 * type pos_or_zero = +{d0 : pos, p1 : pos_or_zero, e : 1}
 *)

proc dbl0 : int |- int   % 2n+0
proc dblp1 : int |- int  % 2n+1
proc dblm1 : int |- int  % 2n-1

% assume left is positive, negative, or zero, right is also
proc dbl0 = caseL ( d0 => R.d0 ; R.d0 ; <->
                  | p1 => R.d0 ; R.p1 ; <->
                  | m1 => R.d0 ; R.m1 ; <->
                  | e => R.e ; <-> )
proc dblp1 = R.p1 ; <->         % assume left is positive or zero, right is positive
proc dblm1 = R.m1 ; <->         % assume left is negative or zero, right is negative

% assume left is negative, ensure right will be negative or zero
proc succ_neg : int |- int
proc succ_neg = caseL ( d0 => succ_neg || dblm1 % 2n+1 = 2(n+1)-1
                      | p1 => succ_neg || dbl0  % (2n+1)+1 = 2(n+1)+0 IMPOSSIBLE!
                      | m1 => dbl0              % (2n-1)+1 = 2n+0
                      | e => R.p1 ; R.e ; <-> ) % IMPOSSIBLE!

% assume left is positive, right will be positive or zero
proc pred_pos : int |- int
proc pred_pos = caseL ( d0 => pred_pos || dblp1 % (2n+0)-1 = 2(n-1)+1
                      | p1 => dbl0              % (2n+1)-1 = 2(n+0)+0
                      | m1 => pred_pos || dbl0  % (2n-1)-1 = 2(n-1)+0 IMPOSSIBLE!
                      | e => R.m1 ; R.e ; <-> ) % IMPOSSIBLE!

% send sign, followed by the standard form of the left
proc norm : int |- sign_test
proc norm = caseL ( d0 => norm || caseL ( zero => R.zero ; <->           % or: dbl0 || (R.zero ; <->)
                                        | pos =>  R.pos ; R.d0 ; <->
                                        | neg =>  R.neg ; R.d0 ; <-> )
                  | p1 => norm || caseL ( zero => R.pos ; R.p1 ; <->
                                        | pos =>  R.pos ; R.p1 ; <->
                                        | neg =>  succ_neg || dblm1 || (R.neg ; <->) )  % 2n+1 = 2(n+1)-1, n neg
                  | m1 => norm || caseL ( zero => R.neg ; R.m1 ; <->
                                        | pos =>  pred_pos || dblp1 || (R.pos ; <->)    % 2n-1 = 2(n-1)+1, n pos
                                        | neg =>  R.neg ; R.m1 ; <-> )
                  | e => R.zero ; R.e ; <-> )

(************)
(* Examples *)
(************)

proc ex3a : int
proc ex3a = zero || succ || succ || succ
exec ex3a

proc ex3b : int
proc ex3b = ex3a || pred || succ
exec ex3b

proc ex3c : int
proc ex3c = ex3a || succ || pred
exec ex3c

proc exm3 : int
proc exm3 = ex3c || neg
exec exm3

proc ex3pos : sign
proc ex3pos = ex3c || neu2sign
exec ex3pos

proc exm3neg : sign_test
proc exm3neg = exm3 || sgn_test
exec exm3neg

proc exm3norm : sign_test
proc exm3norm = exm3 || norm
exec exm3norm

proc exm1 : int
proc exm1 = ex3c || pred || pred || pred || pred
exec exm1

proc exm1neg : sign
proc exm1neg = exm1 || neu2sign
exec exm1neg

proc exm1norm : sign_test
proc exm1norm = exm1 || norm
exec exm1norm
