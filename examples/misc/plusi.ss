#options --syntax=implicit --terminate=equi
#test success

type nat{n} = +{zero : ?{n = 0}. 1,
                succ : ?{n > 0}. nat{n-1}}

type plus{x}{y}{z} = +{plus0 : ?{x = 0}. ?{y = z}. 1,
                       pluss : ?{x > 0}. ?{z > 0}. plus{x-1}{y}{z-1}}

proc thm{n} : nat{n} |- plus{n}{0}{n}
proc thm{n} =
   caseL ( zero => R.plus0 ; waitL ; closeR
         | succ => R.pluss ; thm{n-1} )
