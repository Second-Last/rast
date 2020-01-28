#options --time=none --work=send --syntax=explicit

type nat = +{ z : 1,
              s : nat }
type ctr = &{ inc : <|<|ctr,
              dec : +{ z : 1,
                       s : ctr },
              val : <|<|nat }
proc zero : . |{2}- ctr
proc succ : ctr |{2}- ctr

proc zero = caseR ( inc => getR ; getR ;
                           zero || succ
                  | dec => R.z ;
                           closeR
                  | val => getR ; getR ;
                           R.z ;
                           work ; work ;
                           closeR )

proc succ = caseR ( inc => getR ; getR ;
                           succ || succ
                  | dec => R.s ;
                           work ;
                           <->
                  | val => getR ; getR ;
                           R.s ;
                           L.val ;
                           payL ;
                           payL ;
                           <-> )

proc cfive : . |{15}- ctr
proc cfive = (zero ||
              succ ||
              succ)
             [|{6}- ctr]
             (L.inc ;
             payL ;
             payL ;
             L.inc ;
             payL ;
             payL ;
             L.inc ;
             payL ;
             payL ;
             <->)
exec cfive

proc five : . |{18}- nat
proc five = cfive ||
            L.val ; payL ; payL ; <->
exec five

proc four : . |{21}- nat
proc four = cfive ||
            (L.dec ;
             caseL ( z => waitL ;
                          zero
                   | s => work ;
                          work ;
                          <-> ))
             [|{3}- ctr]
             L.val ; payL ; payL ; <->
exec four
