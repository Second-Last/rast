#options --syntax=explicit
#test success

type nat{n} = +{z:?{n=0}.1, s:?{n>0}. +{z:?{n=1}.1, s:?{n>1}.nat{n-2}}}
type nat'{k} = +{z:?{k=0}.1, s:?{k>0}. nat'{k-1}}
eqtype nat{n} = nat'{n}

proc fwd : nat{17} |- nat'{17}
proc fwd = <->
