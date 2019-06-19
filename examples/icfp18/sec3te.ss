#options --time=none --syntax=explicit
#test success

% Ticks are inserted here by the programmer
% instead of the interpreter for pedagogical purposes

type bits = +{b0 : ()bits, b1 : ()bits, $ : ()1}

proc copy : bits |- ()bits
proc copy = caseL ( b0 => tick ; R.b0 ; copy
                  | b1 => tick ; R.b1 ; copy
                  | $ => tick ; R.$ ; waitL ; tick ; closeR )

proc plus1 : bits |- ()bits
(*
proc plus1 = caseL ( b0 => tick ; R.b1 ; <->   % type error here
                   | b1 => tick ; R.b0 ; plus1
                   | $ => tick ; R.$ ; waitL ; tick ; closeR )
*)
proc plus1 = caseL ( b0 => tick ; R.b1 ; copy
                   | b1 => tick ; R.b0 ; plus1
                   | $ => tick ; R.$ ; waitL ; tick ; closeR )

proc plus2 : bits |- ({2}) bits
proc plus2 = plus1 || (delay ; plus1)

proc six : bits
proc six = R.b0 ; delay ; R.b1 ; delay ; R.b1 ; delay ; R.$ ; delay ; closeR
exec six

type sbits = +{b0 : ()sbits, b1 : ()<>sbits, $ : ()1}

proc compress : bits |- ()sbits
proc skip1s : bits |- ()<>sbits
proc compress = caseL ( b0 => tick ; R.b0 ; compress
                      | b1 => tick ; R.b1 ; skip1s
                      | $ => tick ; R.$ ; waitL ; tick ; closeR )
proc skip1s = caseL ( b0 => tick ; nowR ; R.b0 ; compress
                    | b1 => tick ; (skip1s || idle)
                    | $ => tick ; nowR ; R.$ ; waitL ; tick ; closeR )

proc idle : ()<>sbits |- <>sbits
proc idle = delay ; <->

proc example : ()sbits
proc example = (R.b0 ; delay ; R.b0 ; delay ; R.b1 ; delay ; R.b1 ; delay ; R.b1 ; delay ;
                R.b0 ; delay ; R.b1 ; delay ; R.b1 ; delay ; R.$ ; delay ; closeR)
                [bits]
                compress
exec example

type ctr = []&{inc : ()ctr, val : ()bits}
proc bit0 : ()ctr |- ctr
proc bit1 : ctr |- ctr
proc empty : . |- ctr

proc bit0 = whenR ;
            caseR ( inc => tick ; bit1
                  | val => tick ; R.b0 ; nowL ; L.val ; <-> )
proc bit1 = whenR ;
            caseR ( inc => tick ; nowL ; L.inc ; bit0
                  | val => tick ; R.b1 ; nowL ; L.val ; <-> )
proc empty = whenR ;
             caseR ( inc => tick ; empty || bit1
                   | val => tick ; R.$ ; delay ; closeR )

proc client : ctr |- ({1}) ctr

proc client = nowL ; L.inc ; <->

