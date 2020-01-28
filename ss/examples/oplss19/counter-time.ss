#options --time=recv

type bin = +{b0 : ()bin, b1 : ()bin, e : ()1}

proc copy : bin |- ()bin
proc copy = caseL ( b0 => R.b0 ; copy
                  | b1 => R.b1 ; copy
                  | e => R.e ; waitL ; closeR )

proc plus1 : bin |- ()bin
proc plus1 = caseL ( b0 =>          % ()bin |- ()bin
                                    %   bin |- bin
                     R.b1 ;         %   bin |- ()bin
                     copy
                   | b1 => R.b0 ; plus1
                   | e => R.b1 ; waitL ; R.e ; closeR )

proc six : bin
proc six = R.b0 ; R.b1 ; R.b1 ; R.e ; closeR
exec six

proc eight : ()()bin
proc eight = six || plus1 || plus1
exec eight

(*
type sbits = +{b0 : ()<>sbits, b1 : ()<>sbits, e : ()1}
proc compress : bin |- ()<>sbits
*)