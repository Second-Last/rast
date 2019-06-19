#options --syntax=explicit
#test success

% succeeds with lemma

type nat{n} = +{z:?{n=0}.1, s:?{n>0}. nat2{n-1}}
type nat2{m} = +{z:?{m=0}.1, s:?{m>0}.nat{m-1}}
type nat'{k} = +{z:?{k=0}.1, s:?{k>0}. nat'{k-1}}
eqtype nat{n} = nat'{n}

proc fwd : nat{17} |- nat'{17}
proc fwd = <->
