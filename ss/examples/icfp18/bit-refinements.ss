#options --time=none --syntax=explicit
#test success

type rbits{r} = +{b0 : ({r+2}) rbits{r}, b1 : ({r+2}) rbits{r}, $ : ({r+2}) 1}

proc copy{r} : rbits{r} |- ()rbits{r}
proc copy{r} = caseL ( b0 => tick ; R.b0 ; delay {r+1} ; copy{r}
                  | b1 => tick ; R.b1 ; delay {r+1} ; copy{r}
                  | $ => tick ; R.$ ; delay {r+1} ; waitL ; tick ; closeR )

proc plus1{r} : rbits{r} |- ()rbits{r}
proc plus1{r} = caseL ( b0 => tick ; R.b1 ; delay {r+1} ; copy{r}
                   | b1 => tick ; R.b0 ; delay {r+1} ; plus1{r}
                   | $ => tick ; R.$ ; delay {r+1} ; waitL ; tick ; closeR )

proc plus2{r} : rbits{r} |- ()()rbits{r}
proc plus2{k} = plus1{k} || (delay ; plus1{k})