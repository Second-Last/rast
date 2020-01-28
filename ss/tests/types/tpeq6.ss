#options --syntax=explicit
#test success

type nat{n} = +{z:1, s:nat{n+1}}
type nat'{k} = +{z:1, s:nat'{k+1}}
eqtype nat{n} = nat'{k}

proc fwd{m} : nat{m} |- nat'{m}
proc fwd{m} = <->
