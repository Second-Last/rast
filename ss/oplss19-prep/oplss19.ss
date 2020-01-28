#options
#test success

type bits = +{b0 : bits, b1 : bits, e : 1}

proc plus1 : bits |- bits
proc plus1 = caseL ( b0 => R.b1 ; <->
                   | b1 => R.b0 ; plus1
                   | e => R.b1 ; R.e ; waitL ; closeR )

proc six : bits
proc six = R.b0 ; R.b1 ; R.b1 ; R.e ; closeR

proc eight : bits
proc eight = six || plus1 || plus1
exec eight
