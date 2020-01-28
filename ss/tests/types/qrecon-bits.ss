#options --syntax=implicit
#test success

type ubits{n} = +{b0 : ?{n > 0}. ubits{n-1}, $ : ?{n = 0}. 1}

proc elem{n} : ubits{n+1} |- ubits{n}

proc elem{n} = caseL ( b0 => <-> )