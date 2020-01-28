
#options --work=send --syntax=implicit
#test approx success

type list{n} = +{cons : ?{n > 0}. list{n-1}, nil : ?{n = 0}. 1}

proc nil : . |{_a}- list{0}

proc nil = R.nil ; closeR