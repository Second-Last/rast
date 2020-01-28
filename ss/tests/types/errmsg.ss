#options --time=free --syntax=implicit
#test error

% if mixed, work has to come "outside" type

type word{w} = +{e : ?{w = 0}. 1}

proc zero{w} : word{w}
proc zero{w} = R.e ; closeR

