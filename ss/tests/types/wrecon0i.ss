#options --work=send --syntax=implicit
#test success

type one = 1
type get1 = &{get: <| one}

proc finish : one |{1}- one
proc finish = waitL ; closeR

proc test : get1 |{3}- one
proc test = L.get ; finish || <->
