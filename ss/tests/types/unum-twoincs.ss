#options --syntax=explicit
#test success

type odd{n} = +{s : even{n+1}}

type even{n} = +{z : 1, s : odd{n+1}}

proc inco{n} : odd{n+1} |- even{n}

proc inco{n} = caseL( s => R.s ; ince{n+1} )

proc ince{n} : even{n+1} |- odd{n}

proc ince{n} = caseL ( z => R.s ; waitL ; R.z ; closeR 
                     | s => R.s ; inco{n+1} )