#options --work=send --syntax=implicit
#test approx success

type ctr = &{inc : <{_a}| ctr, dec : <{_b}| hd}
type hd = +{s : |{_c}> ctr, z : 1}

proc empty : ctr
proc bit0 : ctr |{_d}- ctr
proc bit0' : hd |{_e}- hd
proc bit1 : ctr |{_f}- ctr

proc empty = caseR ( inc => work {_g}; empty || bit1
                   | dec => work {_h}; R.z ; closeR )
proc bit0 = caseR ( inc => work {_i}; bit1
                  | dec => L.dec ; work {_j}; bit0' )
proc bit0' = caseL ( s => R.s ; work{_k}; bit1 
                   | z => R.z ; work{_l}; waitL ; closeR )
proc bit1 = caseR ( inc => L.inc ; work{_m}; bit0
                  | dec => R.s ; work{_n}; bit0 )

(*
proc decr : ctr |{_g}- ctr
proc decr = L.dec ;
            caseL ( s => <->
                  | z => waitL ; empty )

proc c3 : . |{_h}- ctr
proc c3 = empty || L.inc ; L.inc ; L.inc ; <->
*)

(* for testing purposes *)
(*
type nat = +{z : 1, s : nat}
proc ctr2nat : ctr |- nat
proc hd2nat : hd |- nat

proc ctr2nat = L.dec ; hd2nat
proc hd2nat = caseL ( s => R.s ; ctr2nat
                    | z => R.z ; waitL ; closeR )

proc n3 : nat
proc n3 = c3 || ctr2nat
exec n3

proc n2 : nat
proc n2 = c3 || decr || ctr2nat
exec n2

proc n1 : nat
proc n1 = c3 || decr || decr || ctr2nat
exec n1

proc n0 : nat
proc n0 = c3 || decr || decr || decr || ctr2nat
exec n0
*)