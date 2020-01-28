#options --time=recv --syntax=implicit --terminate=equi
#test success

type bits = +{b0 : ()bits, b1 : ()bits, e : ()1}

proc copy : bits |- ()bits
proc copy = caseL ( b0 => R.b0 ; copy
                  | b1 => R.b1 ; copy
                  | e => R.e ; waitL ; closeR )

proc plus1 : bits |- ()bits
proc plus1 = caseL ( b0 => R.b1 ; copy
                   | b1 => R.b0 ; plus1
                   | e => R.b1 ; waitL ; R.e ; closeR )

proc six : bits
proc six = R.b0 ; R.b1 ; R.b1 ; R.e ; closeR

proc eight : ()()()bits
proc eight = six || plus1 || plus1
exec eight

type sbits = +{b0 : ()<>sbits, b1 : ()<>sbits, e : ()1}

proc compress0 : bits |- ()<>sbits
proc ignore0 : bits |- ()<>sbits

proc compress0 = caseL ( b0 => R.b0 ; ignore0
                       | b1 => R.b1 ; compress0
                       | e => R.e ; waitL ; closeR )
proc ignore0 = caseL ( b0 => ignore0
                     | b1 => R.b1 ; compress0
                     | e => R.e ; waitL ; closeR )

proc x0001001101 : bits
proc x0001001101 = R.b0 ; R.b0 ; R.b0 ; R.b1 ; R.b0 ; R.b0 ; R.b1 ; R.b1 ; R.b0 ; R.b1 ; R.e ; closeR
exec x0001001101

proc x01001101 : ()<>sbits
proc x01001101 = x0001001101 || compress0
exec x01001101
