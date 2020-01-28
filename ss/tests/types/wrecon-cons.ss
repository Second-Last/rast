#options --work=send --syntax=implicit
#test success

type list{n} = +{cons : ?{n > 0}. list{n-1}, nil : ?{n = 0}. 1}

proc cons{n} : list{n+1} |- list{n}

proc cons{n} = caseL ( cons =>  <-> )