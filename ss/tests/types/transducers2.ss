#options --syntax=implicit --time=recv --work=send
#test success

% Finite state transducers

% if mixed, time has to come before work

type stream_t = +{a : ()stream_t, b : ()stream_t}
type stream_wt = +{a : ()|>stream_wt, b : ()|>stream_wt}

proc copy_wt : stream_wt |- ()stream_t
proc copy_wt = caseL ( a => R.a ; copy_wt
                     | b => R.b ; copy_wt )
