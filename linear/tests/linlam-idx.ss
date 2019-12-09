#test success
#options --work=none --time=none --syntax=implicit

(*
eval (lam f) = lam f
eval (app e1 e2) = 
  case eval e1 ( lam f => eval (f e2) ) % no case for app needed
*)

(*
exp{0} = val
exp{1} = exp
*)

type exp{n} = +{ lam : ?{n <= 1}. exp{1} -o exp{1}, % "call-by-name"
                 app : ?{n = 1}. exp{n} * exp{n} }

decl apply : (e1 : exp{1}) (e2 : exp{1}) |- (e : exp{1})
proc e <- apply <- e1 e2 =
  e.app ; send e e1 ; e <- e2

decl lambda : (f : exp{1} -o exp{1}) |- (e : exp{0})
proc e <- lambda <- f =
  e.lam ; e <- f

decl eval : (e : exp{1}) |- (v : exp{0})
proc v <- eval <- e =
  case e ( lam => v <- lambda <- e
         | app => e1 <- recv e ;                    % e = e2
                  v1 <- eval <- e1 ;
                  case v1 ( lam => send v1 e ; v <- eval <- v1 ) )

(* id = \x. x *)
decl id : . |- (e : exp{1})
proc e <- id <- =
  e.lam ; x <- recv e ; e <- x

(* id id *)
decl idid : . |- (e : exp{1})
proc e <- idid <- =
  i1 <- id <- ;
  i2 <- id <- ;
  e <- apply <- i1 i2

(* swap = \f. \x. \y. (f y) x *)
decl swap : . |- (e : exp{1})
proc e <- swap <- =
  e.lam ; f <- recv e ;
  e.lam ; x <- recv e ;
  e.lam ; y <- recv e ;
  fy <- apply <- f y ;
  e <- apply <- fy x
