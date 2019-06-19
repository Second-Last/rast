#options --syntax=explicit
#test success

type one = 1
type iter{n} = !{n > 0}. &{stop: one, next: iter{n+1}}

proc finish{k}{n} : iter{k} |- !{k > 0}. iter{n}
proc finish{k}{n} = assumeR {k > 0} ;
                    assumeR {n > 0} ;
                    caseR ( stop =>           % iter{k} |- one
                            assertL {k > 0} ; % &{stop: one, next: iter{n+1}} |- one
                            L.stop ;          % one |- one
                            waitL ; closeR
                          | next =>           % k > 0; iter{k} |- iter{n+1}
                            finish{k}{n+1} || % !{k > 0}. iter{n+1} |- iter{n+1}
                            assertL {k > 0} ; % iter{n+1} |- iter{n+1}
                            <-> )


