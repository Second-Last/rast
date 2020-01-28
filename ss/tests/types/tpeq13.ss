#options --syntax=explicit
#test error

% these should be distinct since the s message is
% possible for nat{0} (followed by an infinite, internal
% loop) but not for zero.

type nat{n} = +{z:?{n=0}.1, s:?{n>0}. nat{n-1}}
type zero = +{z:?{0=0}.1}

eqtype zero = nat{0}

proc fwd : nat{0} |- zero
proc fwd = <->
