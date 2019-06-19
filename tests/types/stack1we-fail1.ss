#options --work=send --syntax=explicit
#test error

type bits = +{b0 : bits, b1 : bits}

type stack{n} = &{enq : &{b0 : stack{n+1}, b1 : stack{n+1}},
                  deq : +{none : 1,
                          some : +{b0 : stack{n-1}, b1 : stack{n-1}}}}