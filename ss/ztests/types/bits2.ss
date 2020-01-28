#options --time=free --syntax=implicit
#test success

type bits{r}{s} = +{b0 : ({r}) bits{r}{s}, b1 : ({r}) bits{r}{s}, $ : ({s})1}

type ebits = +{b0 : <> ebits, b1 : <> ebits, $ : <>1}

proc copy{r}{s} : bits{r}{s} |- ebits

proc copy{r}{s} =
  caseL ( b0 => R.b0 ; copy{r}{s}
        | b1 => R.b1 ; copy{r}{s}
        | $ => R.$ ; waitL ; closeR)