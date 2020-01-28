#options --syntax=explicit
#test error

type nat{n} = +{z:?{n=0}. 1, s:?{n>0}. nat{n-1}}
type nat'{n} = +{z:?{n=0}. 1, s:?{n>0}. nat'{n-1}}
eqtype nat{n} = nat'{0}

proc fwd{n} : nat{n} |- nat'{n}
proc fwd{n} = <->
