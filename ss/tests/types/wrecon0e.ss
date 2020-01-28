#options --work=send --syntax=explicit
#test success

type one = 1
type get1 = &{get: <| one}

proc finish : one |{1}- one
proc finish = waitL ; closeR

proc test : get1 |{3}- one
proc test = L.get ; payL ; finish || <->
