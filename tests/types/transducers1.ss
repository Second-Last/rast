#options --syntax=implicit --time=recv --work=send
#test error

% Finite state transducers

type stream = +{a : stream, b : stream}

proc copy : stream |- stream
proc copy = caseL ( a => R.a ; copy
                  | b => R.b ; copy )

proc ex_aaba : stream |- stream
proc ex_aaba = R.a ; R.a ; R.b ; R.a ; <->
exec ex_aaba

type stream_t = +{a : ()stream_t, b : ()stream_t}
proc copy_t : stream_t |- () stream_t
proc copy_t = caseL ( a => R.a ; copy_t
                    | b => R.b ; copy_t )

