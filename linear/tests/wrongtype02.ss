#options --syntax=implicit
#test error

type bin = +{b0 : bin, b1 : bin, e : 1}
type nat = +{succ : nat, zero : 1}

decl succ : (x : nat) |- (y : bin)
proc y <- succ <- x =
  case x ( succ => y <- succ <- x
         | zero => y <- succ <- x )
