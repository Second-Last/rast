#options --syntax=implicit
#test error

type bin = +{b0 : bin, b1 : bin, e : 1}
type nat = +{succ : nat, zero : 1}

decl succ : (x : nat) (y : nat) |- (z : bin)
proc z <- succ x y =
  case x ( succ => z <- succ y x 
         | zero => z <- succ x y )
