#options --syntax=explicit

type queue{l}{r} = &{enq : queue{l+1}{r},
                    deq : !{r = 0}. +{none : ?{l = 0}. 1,
                                      some : ?{l > 0}. queue{l-1}{0}},
                    del : !{r > 0}. queue{l}{r-1}}

proc elem{l}{r} : queue{l}{r+1} |- queue{l+1}{r}

proc empty{r} : queue{0}{r}

proc elem{l}{r} = caseR ( enq => L.enq ; elem{l+1}{r}
                        | deq => assumeR {r = 0} ; R.some ; assertR {l+1 > 0} ; L.del ; assertL {1 > 0} ; <->
                        | del => assumeR {r > 0} ; L.del ; assertL {r+1 > 0} ; elem{l}{r-1} )

proc empty{r} = caseR ( enq => empty{r+1} || elem{0}{r} 
                      | deq => assumeR {r = 0} ; R.none ; assertR {0 = 0} ; closeR
                      | del => assumeR {r > 0} ; empty{r-1} )

proc zero : queue{0}{0}

proc zero = empty{0}

proc enq3 : queue{0}{0} |- queue{3}{0}

proc enq3 = L.enq ; L.enq ; L.enq ; <->

proc three : queue{3}{0}

proc three = zero || enq3

exec three

proc deq1{l} : queue{l+1}{0} |- queue{l}{0}

proc deq1{l} = L.deq ; assertL {0 = 0} ; caseL ( none => impossibleL {l+1 = 0}
                                               | some => assumeL {l+1 > 0} ; <-> )

proc deq0 : queue{0}{0} |- 1

proc deq0 = L.deq ; assertL {0 = 0} ; caseL ( none => assumeL {0 = 0} ; waitL ; closeR
                                            | some => impossibleL {0 > 0} )

proc two : queue{2}{0}

proc two = three || deq1{2}

exec two

proc one : queue{1}{0}

proc one = two || deq1{1}

exec one

proc zero' : queue{0}{0}

proc zero' = one || deq1{0}

exec zero'

proc zero_deq : 1

proc zero_deq = zero' || deq0

exec zero_deq