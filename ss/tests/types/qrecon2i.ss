#options --syntax=implicit
#test success

type one = 1
type iter{n} = !{n > 0}. &{stop: one, next: iter{n+1}}

proc finish{n} : one |- iter{n}
proc finish{n} = caseR (stop => <-> | next => finish{n+1})

proc test : iter{3} |- one
proc test = L.next ; L.next ; L.stop ; <->

