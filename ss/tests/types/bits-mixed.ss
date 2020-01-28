#options --time=recv --work=send --syntax=implicit
#test success

type bitsi = +{b0 : |>() bitsi, b1 : ()|> bitsi, $ : ()|>|> 1}

type bitso = +{b0 : () bitso, b1 : ()<> bitso, $ : ()1}

proc compress : bitsi |- ()bitso
proc skip1s : bitsi |- ()<>bitso