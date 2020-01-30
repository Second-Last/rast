#test success
#options --work=free --time=none --syntax=implicit

%%% work = number of reductions analysis based on
%%% stored potential.  In the linear lambda-calculus,
%%% every lambda can be reduced at most once, so if
%%% we are counting reductions it should carry potential 1.
%%% For this cost model we specify work=free and insert
%%% the "work" manually where the reduction takes place.

(*
eval (lam f) = lam f
eval (app e1 e2) = 
  case eval e1 ( lam f => eval (f e2) ) % no case for app needed
*)

type exp = +{ lam : |> exp -o exp,
              app : exp * exp }
              
type val = +{ lam : |> exp -o exp }

decl apply : (e1 : exp) (e2 : exp) |- (e : exp)
proc e <- apply e1 e2 =
  e.app ; send e e1 ; e <-> e2

decl lambda : (f : exp -o exp) |{1}- (v : val)
proc v <- lambda f =
  v.lam ; v <-> f

decl eval : (e : exp) |- (v : val)
proc v <- eval e =
  case e ( lam => v <- lambda e
         | app => e1 <- recv e ; % e = e2
                  v1 <- eval e1 ;
                  case v1 ( lam => work ; % next message corresponds to beta-reduction
                                   send v1 e ;
                                   v <- eval v1 ) )

(* id = \x. x *)
decl id : . |{1}- (e : exp)
proc e <- id =
  e.lam ; x <- recv e ; e <-> x

(* id id *)
decl idid : . |{2}- (e : exp)
proc e <- idid =
  i1 <- id ;
  i2 <- id ;
  e <- apply i1 i2

(* swap = \f. \x. \y. (f y) x *)
decl swap : . |{3}- (e : exp)
proc e <- swap =
  e.lam ; f <- recv e ;
  e.lam ; x <- recv e ;
  e.lam ; y <- recv e ;
  fy <- apply f y ;
  e <- apply fy x
