#options --syntax=explicit
#test success

type nat{n} = +{z:?{n=0}.1}
type zero = +{z:?{0=0}.1}

proc fwd : nat{0} |- zero
proc fwd = <->
