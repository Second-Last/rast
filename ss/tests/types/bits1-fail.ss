#options --time=free --syntax=explicit
#test error

type bits{r}{s} = +{b0 : ({r}) bits{r}{s}, b1 : ({r}) bits{r}{s}, $ : ({s})1}

proc copy{r}{s} : bits{r}{s} |- bits{r}{s}

proc copy{r}{s} =
  caseL ( b0 => R.b0 ; copy
        | b1 => R.b1 ; copy
        | $ => R.$ ; waitL ; closeR)