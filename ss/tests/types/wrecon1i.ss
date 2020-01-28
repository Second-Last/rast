#options --work=send --syntax=implicit
#test success

type one = 1
type get{n} = !{n > 0-1}. &{get: <{n}| one}

proc finish : one |{1}- one
proc finish = waitL ; closeR

proc test{n} : get{n} |{n+2}- one
proc test{n} = L.get ; finish || <->
