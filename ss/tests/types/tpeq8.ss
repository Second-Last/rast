#options --syntax=explicit
#test success

type nat{n} = +{z:1, s:nat{n+2}}
type nat'{k} = +{z:1, s:nat'{k+1}}
eqtype nat{n} = nat'{k}

proc fwd{m} : nat{17} |- nat'{42}
proc fwd{m} = <->
