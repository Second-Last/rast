#options --work=send --syntax=implicit
#test success

type bits = +{b0 : bits, b1 : bits, $ : 1}

type queue = &{enq : &{b0 : <{p}| queue, b1 : <{(p)}| queue},
                  val : <|<| bits}
