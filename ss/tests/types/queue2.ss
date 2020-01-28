#options --work=none --syntax=explicit
#test success

type queue = &{enq : &{b0 : queue, b1 : queue},
               deq : +{$ : 1, b0 : queue, b1 : queue}}

proc bit0 : queue |- queue
proc bit1 : queue |- queue
proc empty : . |- queue

proc bit0 = caseR ( enq => caseR ( b0 => L.enq ; L.b0 ; bit0
                                 | b1 => L.enq ; L.b1 ; bit0 )
                  | deq => R.b0 ; <-> )
proc bit1 = caseR ( enq => caseR ( b0 => L.enq ; L.b0 ; bit1
                                 | b1 => L.enq ; L.b1 ; bit1 )
                  | deq => R.b1 ; <-> )
proc empty = caseR ( enq => caseR ( b0 => empty || bit0
                                  | b1 => empty || bit1 )
                   | deq => R.$ ; closeR )

