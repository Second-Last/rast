#options --syntax=explicit
#test error

type nat{n} = +{z:?{n=0}.1, s:?{n>0}. nat{n-1}}
type zero = +{z:1}

eqtype zero = nat{0}

proc fwd : nat{0} |- zero
proc fwd = <->