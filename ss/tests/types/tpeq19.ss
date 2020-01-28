#options --syntax=explicit
#test success

type nat{n} = +{z:1, s:nat{n+1}}
type bare_nat = +{z:1, s:bare_nat}

% symmetry necessary
eqtype nat{n} = bare_nat
% eqtype bare_nat = nat{n}

proc fwd : bare_nat |- nat{7}
proc fwd = <->
