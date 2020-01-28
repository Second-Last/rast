#options --time=recv --syntax=explicit
#test success

type queue{n} = []&{ins : `({2*n}) +{ack : `queue{n+1}}}

proc empty : . |- queue{0}

proc empty = whenR ; caseR (ins => delay {0} ; R.ack ; delay ; empty || elem{0} )

proc elem{n} : queue{n} |- queue{n+1}

proc elem{n} = whenR ; caseR (ins => nowL ; L.ins ; delay ; delay {2*n} ; caseL (ack => R.ack ; delay ; elem{n+1}))
