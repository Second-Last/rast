#options --work=none --syntax=explicit
#test success

type ctr1{n} = &{inc : ctr1{n+1}}
type ctr2{n} = &{inc : ctr2{n+2}}

proc fwd{m}{n} : ctr1{m} |- ctr2{n}

proc fwd{m}{n} = <->