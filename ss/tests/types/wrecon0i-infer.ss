#options --work=send --syntax=implicit
#test approx success

type one = 1
type get1 = &{get: <| one}

proc finish : one |{_a}- one
proc finish = waitL ; closeR

proc test : get1 |{_b}- one
proc test = L.get ; finish || <->
