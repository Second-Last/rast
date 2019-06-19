#options --syntax=implicit
#test error

% see qrecon3i.ss
% should fail because reconstruction would need to
% insert a spawn or cut with an assertL {...} ; <->
% on the right

type one = 1
type iter{n} = !{n > 0}. &{stop: one, next: iter{n+1}}

proc finish{k}{n} : iter{k} |- !{k > 0}. iter{n}
proc finish{k}{n} = caseR (stop => L.stop ; waitL ; closeR
                         | next => finish{k}{n+1})


