#test success
#options --work=none --time=none --syntax=implicit

% linear lambda-calculus with "subtyping"

(*
eval (lam f) = lam f
eval (app e1 e2) = 
  case eval e1 ( lam f => eval (f e2)
               | app e11 e12 =>  app (app e11 e12) e2 )
*)

type exp = +{ lam : exp -o exp,
              app : exp * exp }
              
type val = +{ lam : exp -o exp }

decl apply : (e1 : exp) (e2 : exp) |- (e : exp)
proc e <- apply <- e1 e2 =
  e.app ; send e e1 ; e <- e2

decl lambda : (f : exp -o exp) |- (v : val)
proc v <- lambda <- f =
  v.lam ; v <- f

decl eval : (e : exp) |- (v : val)
proc v <- eval <- e =
  case e ( lam => v <- lambda <- e
         | app => e1 <- recv e ; % e = e2
                  v1 <- eval <- e1 ;
                  case v1 ( lam => send v1 e ;
                                   v <- eval <- v1 ) )

(* id = \x. x *)
decl id : . |- (e : exp)
proc e <- id <- =
  e.lam ; x <- recv e ; e <- x

(* id id *)
decl idid : . |- (e : exp)
proc e <- idid <- =
  i1 <- id <- ;
  i2 <- id <- ;
  e <- apply <- i1 i2

(* swap = \f. \x. \y. (f y) x *)
decl swap : . |- (e : exp)
proc e <- swap <- =
  e.lam ; f <- recv e ;
  e.lam ; x <- recv e ;
  e.lam ; y <- recv e ;
  fy <- apply <- f y ;
  e <- apply <- fy x
