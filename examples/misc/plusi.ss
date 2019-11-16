#options --syntax=implicit --terminate=equi
#test success

type nat{n} = +{zero : ?{n = 0}. 1,
                succ : ?{n > 0}. nat{n-1}}

type plus{x}{y}{z} = +{plus0 : ?{x = 0}. ?{y = z}. 1,
                       pluss : ?{x > 0}. ?{z > 0}. plus{x-1}{y}{z-1}}

proc zerop : . |- nat{0}
proc zerop = R.zero ; closeR

(* n + 0 = n *)
proc thm1{n} : nat{n} |- plus{n}{0}{n}
proc thm1{n} =
   caseL ( zero => R.plus0 ; waitL ; closeR
         | succ => R.pluss ; thm1{n-1} )

(* n + s(k) = s(n + k) *)
proc thm2{n}{k} : nat{n} |- plus{n}{k+1}{(k+n)+1}
proc thm2{n}{k} =
   caseL ( zero => R.plus0 ; waitL ; closeR
         | succ => R.pluss ; thm2{n-1}{k} )

(* can't prove the next theorem because the subsingleton
 * fragment does not allow nat{k} and nat{n} to be in the
 * context
 *)
(* n + k = k + n *)
(*
proc thm3{n}{k} : nat{k} |- plus{n}{k}{k+n}
proc thm3{n}{k} =
   caseL ( zero => waitL ; zerop || thm1{n}
         | succ => R.pluss ; thm2{n}{k-1} || thm3{n}{k} )
*)

(* brute force, not providing a proof *)
proc thm4{n}{k} : nat{k+n} |- nat{n+k}
proc thm4{n}{k} = <->

proc thm5{n}{k} : nat{n} |- plus{n}{k}{n+k}
proc thm5{n}{k} = caseL ( zero => R.plus0 ; <->
                        | succ => R.pluss ; thm5{n-1}{k} )

type mult{x}{y}{z} = +{mult0 : ?{x = 0}. ?{z = 0}. 1,        % 0 * y = 0
                       mults : ?{x > 0}. ?{z >= y}. mult{x-1}{y}{z-y}}  % (x-1)*y = x*y - y

(* n * 0 = 0 *)
proc thm6{n} : nat{n} |- mult{n}{0}{0}
proc thm6{n} = caseL ( zero => R.mult0 ; <->
                     | succ => R.mults ; thm6{n-1} )

(* n * (k+1) = n * k + n *)
proc thm7{n}{k}{nk} : mult{n}{k}{nk} |- mult{n}{k+1}{nk + n}
proc thm7{n}{k}{nk} =
  caseL ( mult0 => R.mult0 ; <->
        | mults => thm7{n-1}{k}{nk-k} ||
                   R.mults ;
                   <-> )