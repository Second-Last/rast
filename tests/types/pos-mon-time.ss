#options --time=none --syntax=explicit

type list{r} = +{cons : ({r+2}) list{r}, nil : 1}

proc pos_mon{k} : list{k} |- ()list{k}

proc pos_mon{n} =
  caseL ( cons => tick ; R.cons ; delay {n+1} ; pos_mon{n}
        | nil => waitL ; delay ; R.nil ; closeR )
