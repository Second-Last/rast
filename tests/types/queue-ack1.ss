#options --time=recv --syntax=explicit
#test error

type queue{n} = []&{ins : `({2*n}) +{ack : `queue{n+1}}}

proc id{n} : ({2*n}) queue{n} |- ({n}) queue{n}

proc id{n} = delay {n} ; <->
