#options --time=none --work=none --syntax=explicit

type nat = +{ z : 1, s : nat }
type ctr = &{ inc : ctr,
              dec : +{z : 1, s : ctr},
              val : nat }

proc zero :   . |- ctr
proc succ : ctr |- ctr

proc zero = caseR ( inc => zero || succ
                  | dec => R.z ; closeR
                  | val => R.z ; closeR )

proc succ = caseR ( inc => succ || succ
                  | dec => R.s ; <->
                  | val => R.s ; L.val ; <-> )

proc cfive : ctr
proc cfive = (zero || succ || succ) [ctr] (L.inc ; L.inc ; L.inc ; <->)
exec cfive

proc five : nat
proc five = cfive || (L.val ; <->)
exec five

proc four : nat
proc four = cfive || (L.dec ; caseL (z => waitL ; zero | s => <->)) [ctr] (L.val ; <->)
exec four
