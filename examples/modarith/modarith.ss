#options --syntax=implicit --terminate=equi
#test success

type word{w} = +{ b0 : ?{w > 0}. word{w-1},
                  b1 : ?{w > 0}. word{w-1},
                  e  : ?{w = 0}. 1 }

proc zero : word{4}
proc zero = R.b0 ; R.b0 ; R.b0 ; R.b0 ; R.e ; closeR

proc copy{w} : word{w} |- word{w}
proc copy{w} = caseL ( b0 => R.b0 ; copy{w-1}
                     | b1 => R.b1 ; copy{w-1}
                     | e  => R.e  ; waitL ; closeR )

proc succ{w} : word{w} |- word{w}
proc succ{w} = caseL ( b0 => R.b1 ; copy{w-1}
                     | b1 => R.b0 ; succ{w-1}
                     | e  => R.e ; waitL ; closeR ) % mod 2^w!

proc pred{w} : word{w} |- word{w}
proc pred{w} = caseL ( b0 => R.b1 ; pred{w-1}
                     | b1 => R.b0 ; copy{w-1}
                     | e  => R.e ; waitL ; closeR )

proc minus_one : word{4}
proc minus_one = zero || pred{4}
exec minus_one
