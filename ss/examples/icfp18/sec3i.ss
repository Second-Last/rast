#options --time=recv --syntax=implicit

type bits = +{b0 : ()bits, b1 : ()bits, $ : ()1}

proc copy : bits |- ()bits
proc copy = caseL ( b0 =>  R.b0 ; copy
                  | b1 =>  R.b1 ; copy
                  | $ =>  R.$ ; waitL ; closeR )

proc plus1 : bits |- ()bits

proc plus1 = caseL ( b0 =>  R.b1 ; copy
                   | b1 =>  R.b0 ; plus1
                   | $ =>  R.$ ; waitL ;  closeR )

proc plus2 : bits |- ()()bits
proc plus2 = plus1 || (delay ; plus1)

proc six : bits
proc six = R.b0 ; R.b1 ; R.b1 ; R.$ ; closeR
exec six

type sbits = +{b0 : ()sbits, b1 : ()<>sbits, $ : ()1}

proc compress : bits |- ()sbits
proc skip1s : bits |- ()<>sbits
proc compress = caseL ( b0 =>  R.b0 ; compress
                      | b1 =>  R.b1 ; skip1s
                      | $ =>  R.$ ; waitL ;  closeR )
proc skip1s = caseL ( b0 =>  R.b0 ; compress
                    | b1 =>  skip1s
                    | $ =>   R.$ ; waitL ;  closeR )

proc example : ()sbits
proc example = (R.b0 ; R.b1 ; R.b1 ; R.$ ; closeR)
                [bits]
                compress
exec example

type ctr = []&{inc : ()ctr, val : ()bits}
proc bit0 : ()ctr |- ctr
proc bit1 : ctr |- ctr
proc empty : . |- ctr

proc bit0 = caseR ( inc => bit1
                  | val => R.b0 ; L.val ; <-> )
proc bit1 = caseR ( inc => L.inc ; bit0
                  | val => R.b1 ; L.val ; <-> )
proc empty = caseR ( inc => empty || bit1
                   | val => R.$ ; closeR )
