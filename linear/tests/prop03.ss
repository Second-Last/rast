#test error

type X{n} = +{l:?{n > n > 0}. 1}
type Y{n} = +{l:?{0 < n}. 1}

decl f{n} : (x:X{n}) |- (y:Y{n})
proc y <- f{n} <- x = y <- x