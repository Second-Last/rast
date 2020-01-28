#options --syntax=explicit
#test error

type nat{n} = +{z:1, s:nat{n+1}}
type bare_nat = +{z:1, s:bare_nat}

% unnecessary
% eqtype nat{n} = bare_nat

proc fwd : bare_nat |- nat{7}
proc fwd = <->
