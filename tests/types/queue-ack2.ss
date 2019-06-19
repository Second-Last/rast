#options --time=recv --syntax=explicit
#test success

type queue1{n} = []&{ins : `({2*n}) +{ack : `queue1{n+1}}}
type queue2{n} = []&{ins : `({2*n}) +{ack : `queue2{n+1}}}

proc id{n} : queue1{n} |- queue2{n}

proc id{n} = <->
