#options --syntax=explicit
#test error

% this should fail, because the 's' message is possible
% for nat{0}, but not for zero, enve though nat{0} could
% not continue

type nat{n} = +{z:?{n=0}.1, s:?{n>0}. nat{n-1}}
type zero = +{z:?{0=0}.1}

% eqtype zero = nat{0}

proc fwd : nat{0} |- zero
proc fwd = <->
