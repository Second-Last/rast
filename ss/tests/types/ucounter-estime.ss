#options --time=recv --work=none --syntax=explicit

type nat = +{ z : `1, s : `nat }
type ctr = &{ inc : `[]ctr,
              dec : `+{z : `1, s : `[]ctr},
              val : `nat }

proc zero :     . |- []ctr
proc succ : []ctr |- []ctr

proc zero = whenR ;
            caseR ( inc => zero || succ
                  | dec => R.z ; delay ; closeR
                  | val => R.z ; delay ; closeR )

proc succ = whenR ;
            caseR ( inc => succ || succ
                  | dec => R.s ; delay ; <->
                  | val => R.s ; 
                           nowL ; L.val ; 
                           delay ; <-> )

proc cfive : ()()()[]ctr
proc cfive = zero || succ || succ ||
     (nowL ; L.inc ; delay ; nowL ; L.inc ; delay ; nowL ; L.inc ; delay ; <->)
exec cfive

proc five : ()()()()nat
proc five = cfive || (delay ; delay ; delay ; nowL ; L.val ; delay ; <->)
exec five

proc decr : []ctr |- ()()()[]ctr
proc decr = (nowL ; L.dec ; delay ; caseL (z => waitL ; zero | s => delay ; <->))

proc decr3d : ()()()[]ctr |- ()()()()()()[]ctr
proc decr3d = delay ; delay ; delay ; decr

proc four : ()()()()()()()nat
proc four = cfive || decr3d ||
           (delay ; delay ; delay ; delay ; delay ; delay ; nowL ; L.val ; delay ; <->)
exec four
