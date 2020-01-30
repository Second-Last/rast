#test success

type X{n} = +{l:?{~ (n > 0 /\ n < 0)}. 1}
type Y{n} = +{l:?{0 = 0}. 1}

decl f{n} : (x:X{n}) |- (y:Y{n})
proc y <- f{n} x = y <-> x
