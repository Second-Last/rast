#options --syntax=implicit
#test error

type one = 1
type iter{n} = !{n > 0}. &{stop: one, next: iter{n+1}}

proc finish{k}{n} : iter{k} |- iter{n}
proc finish{k}{n} = caseR (stop => L.stop ; waitL ; closeR
                         | next => finish{k}{n+1})

% proc test : iter{3} |- one
% proc test = L.next ; L.next ; L.stop ; <->

