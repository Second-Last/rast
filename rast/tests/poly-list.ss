#test error

type list{n} = +{cons : ?{n > 0}. list{n-1}, nil : ?{n = 0}. 1}

eqtype list{n} = list{n-1}