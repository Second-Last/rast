#options --work=none --syntax=explicit
#test success

type ctr1{n} = &{inc : ctr1{n+1}}
type ctr2{n} = &{inc : ctr2{n+2}}

proc fwd{n} : ctr1{n} |- ctr2{n}

proc fwd{n} = <->