#options --work=send --syntax=implicit
#test approx success

type one = 1
type get{n} = !{n > 0-1}. &{get: <{n}| one}

proc finish : one |{_a}- one
proc finish = waitL ; closeR

proc test{n} : get{n} |{_b*n+_bb}- one
proc test{n} = L.get ; finish || <->
