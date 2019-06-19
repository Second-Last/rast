#options --time=free --syntax=implicit
#test success

type bits0{r}{s} = +{b0 : ({r}) bits1{s}{r}, b1 : ({r}) bits1{s}{r}, $ : ({s})1}

type bits1{r}{s} = +{b0 : ({r})bits0{s}{r}, b1 : ({r}) bits1{s}{r}, $ : ({s})1}

proc copy{r}{s} : bits0{r}{s} |- bits0{r}{s}

proc copy{r}{s} =
  caseL ( b0 => R.b0 ; copy{s}{r}
        | b1 => R.b1 ; copy{s}{r}
        | $ => R.$ ; waitL ; closeR)