(* Real numbers in the [-1,+1] interval
 * using a dyadic representation.
 * Follows: Martin Hotzel Escardo,
 * https://www.cs.bham.ac.uk/~mhe/papers/fun2011.lhs
 *)

(*
 * A sequent of digits d_0, d_1, d_2, ... represents the number
 * x = d_0/2 + d_1/4 + d_2/8 + ...
 *)

type I = +{m1 : I, d0 : I, p1 : I}

proc zero : I
proc zero = R.d0 ; zero

proc one : I
proc one = R.p1 ; one

proc half : I
proc half = R.p1 ; zero

proc minusOne : I
proc minusOne = R.m1 ; minusOne

proc minusHalf : I
proc minusHalf = R.m1 ; zero

type I2 = +{m2 : I2, m1 : I2, d0 : I2, p1 : I2, p2 : I2}

(* side calculation

div2 m1 m2 x = (d = -2-2 = -4 : -1 ; div2 (0:x)
div2 m1 m1 x = (d = -2-1 = -3 : -1 : div2 (1:x)
div2 m1 d0 x = (d = -2   = -2 :  0 : div2 (-2:x)
div2 m1 p1 x = (d = -2+1 = -1 :  0 : div2 (-1:x)
div2 m1 p2 x = (d = -2+2 = 0  :  0 : div2 (0:x)

div2 p1 m2 x = (d = 2-2 = 0 : 0 ; div2 (0:x) 
div2 p1 m1 x = (d = 2-1 = 1 : 0 ; div2 (1:x)
div2 p1 d0 x = (d = 2   = 2 : 0 ; div2 (2:x)
div2 p1 p1 x = (d = 2+1 = 3 : 1 ; div2 (-1:x)
div2 p1 p2 x = (d = 2+4 = 4 : 1 ; div2 (0:x)
*)



proc div2 : I2 |- I
proc div2 = caseL ( m2 => R.m1 ; div2
                  | m1 => caseL ( m2 => R.m1 ; (R.d0 ; <->) [I2] div2
                                | m1 => R.m1 ; (R.p1 ; <->) [I2] div2
                                | d0 => R.d0 ; (R.m2 ; <->) [I2] div2
                                | p1 => R.d0 ; (R.m1 ; <->) [I2] div2
                                | p2 => R.d0 ; (R.d0 ; <->) [I2] div2 )
                  | d0 => R.d0 ; div2
                  | p1 => caseL ( m2 => R.d0 ; (R.d0 ; <->) [I2] div2
                                | m1 => R.d0 ; (R.p1 ; <->) [I2] div2
                                | d0 => R.d0 ; (R.p2 ; <->) [I2] div2
                                | p1 => R.p1 ; (R.m1 ; <->) [I2] div2
                                | p2 => R.p1 ; (R.d0 ; <->) [I2] div2 )
                  | p2 => R.p1 ; div2 )

proc dbl2 : I |- I2
proc dbl2 = caseL ( m1 => R.m2 ; dbl2
                  | d0 => R.d0 ; dbl2
                  | p1 => R.p1 ; dbl2 )

proc double : I |- I
proc double = dbl2 || div2

proc ex1 : I
proc ex1 = half || double
% next line does not terminate
% exec ex1
