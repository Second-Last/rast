#options --time=recv --syntax=implicit
#test success

type bits = +{b0 : ()bits, b1 : ()bits, $ : ()1}

proc copy : bits |- ()bits

proc copy = caseL ( b0 => R.b0 ; copy
                  | b1 => R.b1 ; copy
                  | $  => R.$  ; waitL ; closeR )

proc two : . |- bits

proc two = R.b0 ; R.b1 ; R.$ ; closeR

proc two_copy : . |- ()bits

proc two_copy = two || copy

exec two

exec two_copy

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

proc plus1 : bits |- ()bits

proc plus1 = caseL ( b0 => R.b1 ; copy
                   | b1 => R.b0 ; plus1
                   | $  => R.b1 ; waitL ; R.$ ; closeR)

proc three : . |- ()bits

proc three = two || plus1

exec three

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
(*
proc plus2 : bits |- ()()bits

proc plus2 = plus1 || plus1

proc four : . |- ()()bits

proc four = two || plus2

exec four

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type zbits = +{b0 : <>zbits, $ : ()1}

proc filter : bits |- <>zbits

proc filter = caseL ( b0 => R.b0 ; filter
                    | b1 => filter
                    | $  => R.$ ; waitL ; closeR )

proc x : . |- bits

proc x = R.b0 ; R.b1 ; R.b0 ; R.b1 ; R.b1 ; R.b0 ; R.b0 ; R.$ ; closeR

proc filtered_x : . |- <>zbits

proc filtered_x = x || filter

exec filtered_x*)