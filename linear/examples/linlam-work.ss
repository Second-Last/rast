#test success
#options --work=send --time=none --syntax=implicit

%%% work = number of messages; analysis based on
%%% stored potential.
%%% A lambda expression has 2 units of potential, 1 of which is used
%%% to send the 'lam' message, the other for beta-reduction.
%%% An application does not carry potential but forming an
%%% application requires 2 units: 1 to send 'app', and 1 to
%%% send 'e1' before becoming 'e2'.
%%%
%%% The value lambda just requires 1 unit, for the beta-reduction,
%%% that is, sending the argument to the body.
%%%
%%% Overall, we need 3 ergs for each lambda and 2 ergs for each
%%% expression to account for arbitrary evaluation.
%%%
%%% eval requires no external potential

(*
eval (lam f) = lam f
eval (app e1 e2) = 
  case eval e1 ( lam f => eval (f e2) ) % no case for app needed
*)

type exp = +{ lam : |{2}> exp -o exp,
              app : exp * exp }
              
type val = +{ lam : |> exp -o exp }

decl apply : (e1 : exp) (e2 : exp) |{2}- (e : exp)
proc e <- apply e1 e2 =
  e.app ; send e e1 ; e <-> e2

decl lambda : (f : exp -o exp) |{2}- (v : val)
proc v <- lambda f =
  v.lam ; v <-> f

decl eval : (e : exp) |- (v : val)
proc v <- eval e =
  case e ( lam => v <- lambda e
         | app => e1 <- recv e ; % e = e2
                  v1 <- eval e1 ;
                  case v1 ( lam => send v1 e ;
                                   v <- eval v1 ) )

(* id = \x. x *)
decl id : . |{3}- (e : exp)
proc e <- id =
  e.lam ; x <- recv e ;  % 1+2 = 3 ergs
  e <-> x

(* id id *)
decl idid : . |{8}- (e : exp)
proc e <- idid =
  i1 <- id ;  % 3 ergs
  i2 <- id ;  % 3 ergs
  e <- apply i1 i2 % 2 ergs

(* swap = \f. \x. \y. (f y) x *)
decl swap : . |{13}- (e : exp)
proc e <- swap =
  e.lam ; f <- recv e ;  % 1+2 = 3 ergs
  e.lam ; x <- recv e ;  % 3 ergs
  e.lam ; y <- recv e ;  % 3 ergs
  fy <- apply f y ;   % 2 ergs
  e <- apply fy x     % 2 ergs
