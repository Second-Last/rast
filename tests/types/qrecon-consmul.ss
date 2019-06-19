#options --syntax=implicit
#test error

type list{n} = +{cons : ?{n > 0}. list{n-1}, nil : ?{n = 0}. 1}

proc cons{n} : list{n+1} |- list{n}

proc cons{n} = caseL ( cons =>  <-> )

proc cons2{n}{k} : list{n+k+1} |- list{n+1}

proc cons2{n}{k} = cons{n+k} || cons2{n}{k-1}