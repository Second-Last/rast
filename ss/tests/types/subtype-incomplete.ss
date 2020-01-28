#options --time=free --work=none --syntax=implicit
#test success

(* these should both be subtypes *)

(* sub1 by rules [](), []R, []L, refl *)
proc sub1 : []1 |- ()[]1
proc sub1 = <->

(* sub2 by rules []L, ()(), refl *)
proc sub2 : []()1 |- ()1
proc sub2 = <->
