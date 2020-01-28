#options --time=none --syntax=explicit
#test success

type list{r} = +{cons : ({0}) list{r}, nil : 1}

proc P{k} : list{k} |- list{k}

proc P{n} =
  caseL ( cons => R.cons ; P{n})
        | nil => waitL ; R.nil ; closeR )
