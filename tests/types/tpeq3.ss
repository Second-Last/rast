#options --syntax=explicit
#test error

% should fail

type nat = +{z:1,s:nat}
type nat' = +{s:nat'}
eqtype nat = nat'

proc fwd : nat |- nat'
proc fwd = <->
