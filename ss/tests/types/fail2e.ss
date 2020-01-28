#options --time=none --syntax=explicit
#test error

type bits = +{b0 : bits, b1 : bits, $ : 1}

type sbits = +{b0 : `sbits, b1:`<>sbits, $ : `1}

proc inc : bits |- bits
proc inc = caseL ( b0 => R.b1 ; <->
                 | b1 => R.b0 ; inc
                 | $ => R.b1 ; R.$ ; closeR )

% timed version, where we apply the cost model
% manually so it can be in the same file
type tbits = +{b0 : `tbits, b1:`tbits, $ : `1}
proc copy : tbits |- ()tbits
proc copy = caseL ( b0 => tick ; R.b0 ; copy
                  | b1 => tick ; R.b1 ; copy
                  | $ => tick ; R.$ ; waitL ; tick ; closeR )
proc plus1 : tbits |- ()tbits
proc plus1 = caseL ( b0 => tick ; R.b1 ; copy
                   | b1 => tick ; R.b0 ; plus1
                   | $ => tick ; R.b1 ; waitL ; tick ; R.$ ; delay ; closeR )

proc plus2 : tbits |- ()()tbits
proc plus2 = plus1 || (delay ; plus1)

proc three : ()()()tbits
proc three = (R.$ ; delay ; closeR) [tbits] plus2 [()()tbits] (delay ; delay ; plus1)
exec three

proc inc2 : bits |- bits
proc inc2 = inc || inc

proc two : bits
proc two = R.b0 ; R.b1 ; R.$ ; closeR

proc four : . |- bits
proc four = two || inc2

exec four
