#options --syntax=implicit
#test success

%%% Valid circular proof of several small theorems
%%% in arithmetic.  Processes with recursive calls are
%%% circular proofs representing inductive arguments;
%%% processes without are direct.

type nat{n} = +{zero : ?{n = 0}. 1,
                succ : ?{n > 0}. nat{n-1}}

decl zero : . |- (x : nat{0})
proc x <- zero = x.zero ; close x

decl succ {n} : (y : nat{n}) |- (x : nat{n+1})
proc x <- succ{n} y = x.succ ; x <-> y

%%% Theorems about addition
type plus{x}{y}{z} = +{plus0 : ?{x = 0}. ?{y = z}. 1,
                       pluss : ?{x > 0}. ?{z > 0}. plus{x-1}{y}{z-1}}

%%% "Master" theorem
%%% Can be checked since addition is linear
%%% Proceeds by induction on n
decl thm0{n}{k} : (x : nat{n}) |- (p : plus{n}{k}{n+k})
proc p <- thm0{n}{k} x =
  case x ( zero => wait x ; p.plus0 ; close p
         | succ => p.pluss ;
                   p <- thm0{n-1}{k} x )

%%% Remaining theorems below all follow from master theorem
%%% but we provide some alternative proofs

(* 0 + k = k *)
% direct proof
decl thm1{k} : . |- (p : plus{0}{k}{k})
proc p <- thm1{k} =
  p.plus0 ; close p

decl thm1b{k} : . |- (p : plus{0}{k}{k})
% proof using master theorem
proc p <- thm1b{k} =
  z <- zero ;
  p <- thm0{0}{k} z

(* (n+1)+k = (n+k)+1 *)
% proof by rule induction on q : plus n k nk
decl thm2{n}{k}{nk} : (q : plus{n}{k}{nk}) |- (p : plus{n+1}{k}{nk+1})
proc p <- thm2{n}{k}{nk} q =
  case q ( plus0 => p.pluss ; p.plus0 ; p <-> q
         | pluss => p.pluss ; p.pluss ; p <-> q )

(* n + 0 = n *)
% proof by induction on n
decl thm3{n} : (x : nat{n}) |- (p : plus{n}{0}{n})
proc p <- thm3{n} x =
   case x ( zero => p.plus0 ; wait x ; close p
          | succ => p.pluss ; p <- thm3{n-1} x )

(* n + s(k) = s(n + k) *)
% proof by induction on n
decl thm4{n}{k} : (x : nat{n}) |- (p : plus{n}{k+1}{(n+k)+1})
proc p <- thm4{n}{k} x =
   case x ( zero => p.plus0 ; wait x ; close p
          | succ => p.pluss ; p <- thm4{n-1}{k} x )

%%% Theorems about multiplication
%%% Master theorem is no longer linear, so we have to
%%% provide some inductive proofs

type mult{x}{y}{z} = +{mult0 : ?{x = 0}. ?{z = 0}. 1,                   % 0 * y = 0
                       mults : ?{x > 0}. ?{z >= y}. mult{x-1}{y}{z-y}}  % (x-1)*y = x*y - y

(* 0 * k = 0 *)
% direct proof
decl thm6{k} : . |- (p : mult{0}{k}{0})
proc p <- thm6{k} =
  p.mult0 ; close p

(* n * 0 = 0 *)
% proof by induction on n
decl thm7{n} : (x : nat{n}) |- (p : mult{n}{0}{0})
proc p <- thm7{n} x =
  case x ( zero => wait x ; p.mult0 ; close p
         | succ => p.mults ; p <- thm7{n-1} x )

(* (n+1)*k = n*k + k *)
% direct proof
decl thm8{n}{k}{nk} : (q : mult{n}{k}{nk}) |- (p : mult{n+1}{k}{nk+k})
proc p <- thm8{n}{k}{nk} q =
  case q ( mult0 => p.mults ; p.mult0 ; wait q ; close p
         | mults => p.mults ; p.mults ; p <-> q )

(* n*(k+1) = n*k + n *)
% proof by rule induction on q : mult n k nk
decl thm9{n}{k}{nk} : (q : mult{n}{k}{nk}) |- (p : mult{n}{k+1}{nk+n})
proc p <- thm9{n}{k}{nk} q =
  case q ( mult0 => p.mult0 ; wait q ; close p
         | mults => p.mults ;
                    p <- thm9{n-1}{k}{nk-k} q )

%%% Master theorem
%%% This requires some nonlinear constraints:
(*
Trusting: n > 0 |= n*k >= k
Trusting: n > 0 |= (n-1)*k = n*k-k
*)
(*
decl thm10{n}{k} : (x : nat{n}) |- (p : mult{n}{k}{n*k})
proc p <- thm10{n}{k} x =
  case x ( zero => p.mult0 ; wait x ; close p
         | succ => p.mults ;
                   p <- thm10{n-1}{k} x )
*)
