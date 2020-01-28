#options --time=recv --syntax=explicit
#test error

type list{r} = +{cons : ({r+2}) list{r}}

proc posmon{k} : list{k} |- ()list{k}

proc posmon{n} =
  caseL ( cons => posmon{n})
