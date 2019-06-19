#options --work=send --syntax=implicit
#test success

type list{n} = +{cons : ?{n > 0}. list{n-1}, nil : ?{n = 0}. 1}

proc nil : . |{2}- list{0}

proc nil = R.nil ; closeR