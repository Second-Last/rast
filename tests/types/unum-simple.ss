#options --syntax=explicit
#test success

type odd{n} = +{s : even{n+1}}

type even{n} = +{z : 1, s : odd{n+1}}

proc inc{n} : odd{n+1} |- even{n}

proc inc{n} = caseL( s => R.s ; R.s ; <-> )