#options --syntax=explicit
#test error

% currently, we do not allow empty choices, syntactically

type nat = +{z:1, s:+{ }}
type zero = +{z:1}

eqtype zero = nat

proc fwd : nat |- zero
proc fwd = <->
