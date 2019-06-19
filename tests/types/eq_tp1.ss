#options --work=none --syntax=explicit
#test success

type queue1{n} = &{ins : queue1{n+1},
                   del : +{none : ?{n = 0}. 1,
                           some : ?{n > 0}. queue1{n-1}}}

type queue2{n} = &{ins : queue2{n+1},
                   del : +{none : ?{n = 0}. 1,
                           some : ?{n > 0}. queue2{n-1}}}

proc fwd{n} : queue1{n} |- queue2{n}

proc fwd{n} = <->