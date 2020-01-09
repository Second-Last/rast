#test success
#options --work=none --time=none --syntax=implicit

%%% Linear lambda calculus using ideas from HOAS,
%%% Expressions are indexed by their size

%%% This verifies that evaluation does not
%%% increase the size of an expression.  Size here
%%% counts applications and lambda-abstractions.

(*
eval (lam f) = lam f
eval (app e1 e2) = 
  case eval e1 ( lam f => eval (f e2) )
*)

%%% exp{n} = linear lambda-calculus expression of size n
type exp{n} = +{ lam : ?{n > 0}. !n1.exp{n1} -o exp{n1+n-1},
                 app : ?n1. ?n2. ?{n = n1+n2+1}. exp{n1} * exp{n2} }

%%% val{n} = values of size n
type val{n} = +{ lam : ?{n > 0}. !n1.exp{n1} -o exp{n1+n-1} }

decl apply{n1}{n2} : (e1 : exp{n1}) (e2 : exp{n2}) |- (e : exp{n1+n2+1})
proc e <- apply{n1}{n2} <- e1 e2 =
  e.app ; send e {n1} ; send e {n2} ;
  send e e1 ; e <- e2

decl lambda{n2} : (f : !n1. exp{n1} -o exp{n1+n2}) |- (v : val{n2+1})
proc v <- lambda{n2} <- f =
  v.lam ; v <- f

%%% Call-by-name evaluation of closed expressions
decl eval{n} : (e : exp{n}) |- (v : ?k. ?{k <= n}. val{k})  % size of v bounded by n
proc v <- eval{n} <- e =
  case e ( lam => send v {n} ;
                  v <- lambda{n-1} <- e
         | app => {n1} <- recv e ;
                  {n2} <- recv e ;           % n = n1 + n2 + 1
                  e1 <- recv e ;             % e1 : exp{n1}, e = e2 : exp{n2}
                  v1 <- eval{n1} <- e1 ;
                  {k2} <- recv v1 ;          % v1 : val{k2} for some k2 <= n1
                  case v1 ( lam => send v1 {n2} ;
                                   send v1 e ;   % v1 : exp{n2+k2-1}
                                   v2 <- eval{n2+k2-1} <- v1 ; % v2 : val{l} for some l <= n2+k2-1 <= n2+n1-1 = n-2
                                   {l} <- recv v2 ;
                                   send v {l} ; v <- v2
                          )
          )

%%% Some small examples

(* id = \x. x *)
decl id : . |- (e : exp{1})
proc e <- id <- =
  e.lam ;
  {k} <- recv e ;
  x <- recv e ;
  e <- x

(* id id *)
decl idid : . |- (e : exp{3})
proc e <- idid <- =
  i1 <- id <- ;
  i2 <- id <- ;
  e <- apply{1}{1} <- i1 i2

(* swap = \f. \x. \y. (f y) x *)
decl swap : . |- (e : exp{5})
proc e <- swap <- =
  e.lam ; {kf} <- recv e ; f <- recv e ;
  e.lam ; {kx} <- recv e ; x <- recv e ;
  e.lam ; {ky} <- recv e ; y <- recv e ;
  fy <- apply{kf}{ky} <- f y ;
  e <- apply{kf+ky+1}{kx} <- fy x
