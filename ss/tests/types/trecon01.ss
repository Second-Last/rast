#options --time=free --syntax=implicit
#test success

% for now, avoid 1 for testing fragmentary reconstruction

type bits = +{b0: ()bits, b1: ()bits}

proc copy : bits |- ()bits
proc copy = caseL ( b0 => R.b0 ; copy
                  | b1 => R.b1 ; copy )
