#options --time=none --syntax=explicit
#test success

type list{r} = +{cons : ({r+1}) list{r}, nil : 1}

proc pos_mon{k} : list{k} |- ()list{k}

proc pos_mon{n} =
  caseL ( cons => tick ; R.cons ; delay {n} ; pos_mon{n}
        | nil => waitL ; delay ; R.nil ; closeR )
