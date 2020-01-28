type bin = +{b0 : bin, b1 : bin, e : 1}
type ctr = &{inc : ctr, val : bin}

proc bit0 : ctr |- ctr
proc bit1 : ctr |- ctr
proc empty : . |- ctr

proc bit0 = caseR ( inc => bit1
                  | val =>          % ctr |- bin
                           L.val ;  % bin |- bin
                           R.b0 ;   % bin |- bin
                           <-> )
proc bit1 = caseR ( inc => L.inc ; bit0
                  | val => L.val ; R.b1 ; <-> )
proc empty = caseR ( inc => empty || bit1
                   | val => R.e ;   % . |- 1
                            closeR
                   )

proc six : ctr
proc six = empty || bit1 || bit1 || bit0
exec six

proc eight : ctr
proc eight = six || (L.inc ; L.inc ; <->)
exec eight
