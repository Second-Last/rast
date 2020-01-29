#test success
#options --work=none --time=none --syntax=implicit

(*
eval (lam f) = lam f
eval (app e1 e2) = 
  case eval e1 ( lam f => eval (f e2) )
*)

type exp{n} = +{ lam : ?n2. ?{n = n2+1}. !n1.exp{n1} -o exp{n1+n2},
                 app : ?n1. ?n2. ?{n = n1+n2+1}. exp{n1} * exp{n2} }

% value only bounded by n, since we cannot predict size before evaluation
type val{n} = +{ lam : ?n2. ?{n2+1 <= n}. !n1.exp{n1} -o exp{n1+n2} }

decl apply{n1}{n2} : (e1 : exp{n1}) (e2 : exp{n2}) |- (e : exp{n1+n2+1})
proc e <- apply{n1}{n2} e1 e2 =
  e.app ; send e {n1} ; send e {n2} ;
  send e e1 ; e <-> e2

decl lambda{n2} : (f : !n1. exp{n1} -o exp{n1+n2}) |- (v : val{n2+1})
proc e <- lambda{n2} f =
  e.lam ; send e {n2} ;
  e <-> f

decl resize{n}{n'|n' >= n} : (v : val{n}) |- (v' : val{n'})
proc v' <- resize{n}{n'} v =
  case v ( lam => {k1} <- recv v ;
                  v'.lam ;
                  send v' {k1} ;
                  v' <-> v )

decl eval{n} : (e : exp{n}) |- (v : val{n}) % size of v bounded by n
proc v <- eval{n} e =
  case e ( lam => {n2} <- recv e ;
                  v <- lambda{n2} e
         | app => {n1} <- recv e ;
                  {n2} <- recv e ;
                  e1 <- recv e ;         % e1 : exp{n1}, e = e2 : exp{n2}
                  v1 <- eval{n1} e1 ;     % v1 : exp{k} for some k <= n1
                  case v1 ( lam => {k2} <- recv v1 ;
                                   send v1 {n2} ;
                                   send v1 e ;   % v1 : exp{n2+k2}
                                   v2 <- eval{n2+k2} v1 ; % v : exp{l} where l <= n2+k2 = n2+k+1
                                   v <- resize{n2+k2}{n} v2
                             ) )

(* id = \x. x *)
decl id : . |- (e : exp{1})
proc e <- id =
  e.lam ; send e {0};
  {k} <- recv e ;
  x <- recv e ;
  e <-> x

(* id id *)
decl idid : . |- (e : exp{3})
proc e <- idid =
  i1 <- id ;
  i2 <- id ;
  e <- apply{1}{1} i1 i2

(* swap = \f. \x. \y. (f y) x *)
decl swap : . |- (e : exp{5})
proc e <- swap =
  e.lam ; send e {4} ; {kf} <- recv e ; f <- recv e ;
  e.lam ; send e {kf+3} ; {kx} <- recv e ; x <- recv e ;
  e.lam ; send e {kx+kf+2} ; {ky} <- recv e ; y <- recv e ;
  fy <- apply{kf}{ky} f y ;
  e <- apply{kf+ky+1}{kx} fy x
