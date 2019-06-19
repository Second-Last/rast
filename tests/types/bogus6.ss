#options --work=send --syntax=implicit
#test error

type bits = +{b0 : bits, b1 : bits, $ : 1}

type queue = &{enq : &{b0 : <{q q}| queue, b1 : <{(p+q*4)}| queue},
                  val : <{(p+q)*4-3*e+2}| <| bits}
