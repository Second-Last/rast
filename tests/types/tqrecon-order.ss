#options --time=free --syntax=implicit
#test success

% succeeds, by good luck
type in{w} = +{ e : ?{w = 0}. 1 }
type out{w} = +{ e : ?{w = 0}. 1 }

proc copy{w} : in{w} |- out{w}
proc copy{w} = caseL ( e => R.e ; <-> )

% fails, by bad luck
type inr{w} = &{ e : !{w = 0}. 1}
type outl{w} = &{ e : !{w = 0}. 1}

proc pass{w} : outl{w} |- inr{w}
proc pass{w} = caseR ( e => L.e ; <-> )
