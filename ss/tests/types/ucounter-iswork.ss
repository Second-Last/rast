#options --time=none --work=send --syntax=implicit

type nat = +{ z : 1, s : nat }
type ctr = &{ inc : <|<| ctr,
              dec : +{z : 1, s : ctr},
              val : <|<| nat }

proc zero :   . |{2}- ctr
proc succ : ctr |{2}- ctr

proc zero = caseR ( inc => zero || succ
                  | dec => R.z ; closeR
                  | val => R.z ; closeR )

proc succ = caseR ( inc => succ || succ
                  | dec => R.s ; <->
                  | val => R.s ; L.val ; <-> )

(*
A |n- P : B     B |k- Q : C
----------------------------
A |n+k- P {|n- B} Q : C
*)

proc cfive : . |{15}- ctr
proc cfive = zero || succ || succ || (L.inc ; L.inc ; L.inc ; <->)
exec cfive

proc five : . |{18}- nat
proc five = cfive || (L.val ; <->)
exec five

proc decr : ctr |{3}- ctr
proc decr = L.dec ; caseL (z => waitL ; zero | s => <->)

proc four : . |{21}- nat
proc four = cfive || decr || (L.val ; <->)
exec four

