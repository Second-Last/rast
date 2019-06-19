#options --work=send --syntax=implicit
#test success

type bits = +{b0 : bits, b1 : bits, $ : 1}

type queue = &{enq : &{b0 : <{p+q-4}| queue, b1 : <{(p+q*4)}| queue},
                  val : <{(p+q)*4-3*e+2}| <| bits}
