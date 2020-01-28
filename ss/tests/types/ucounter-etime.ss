#options --time=recv --work=none --syntax=explicit

type nat = +{ z : `1, s : `nat }
type ctr = &{ inc : `[]ctr,
              dec : `+{z : `1, s : `[]ctr},
              val : `nat }

proc zero :     . |- []ctr
proc succ : []ctr |- []ctr

proc zero = whenR ;
            caseR ( inc => % . |- []ctr
                    zero || succ
                  | dec => % . |- +{z:`1, s:`[]ctr}
                    R.z ; delay ; closeR
                  | val => % . |- nat
                    R.z ; delay ; closeR )

proc succ = whenR ;
            caseR ( inc => % []ctr |- []ctr
                           succ || succ
                  | dec => % []ctr |- +{z : `1, s: `[]ctr}
                           R.s ; delay ; <->
                  | val =>        % []ctr |- nat
                           R.s ;  % []ctr |- `nat
                           nowL ; L.val ; % `nat |- `nat
                           delay ; <-> )

proc cfive : ()()()[]ctr
proc cfive = (zero || succ || succ) [[]ctr] (nowL ; L.inc ; delay ; nowL ; L.inc ; delay ; nowL ; L.inc ; delay ; <->)
exec cfive

proc five : ()()()()nat
proc five = cfive || (delay ; delay ; delay ; nowL ; L.val ; delay ; <->)
exec five

proc four : ()()()()()()()nat
proc four = cfive || (delay ; delay ; delay ; nowL ; L.dec ; delay ; caseL (z => waitL ; zero | s => delay ; <->))
           [()()()()()()[]ctr] (delay ; delay ; delay ; delay ; delay ; delay ; nowL ; L.val ; delay ; <->)
exec four
