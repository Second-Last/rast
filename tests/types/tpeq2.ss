#options --syntax=explicit
#test success

% should check without consulting environment

type nat = +{z:1,s:nat}
type nat' = +{z:1,s:nat'}
eqtype nat = nat'

proc fwd : nat |- nat'
proc fwd = <->
