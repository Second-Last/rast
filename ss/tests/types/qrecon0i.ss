#options --syntax=implicit
#test success

type one = 1
type get1{n} = &{get: !{n > 0-1}. one}

proc finish{n} : !{n > 0-1}. one |- one
proc finish{n} = waitL ; closeR

proc test : get1{3} |- one
proc test = L.get ; finish{3} || <->