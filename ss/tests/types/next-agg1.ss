#options --time=free --syntax=explicit
#test success

proc id1 : ()()1 |- ({2})1
proc id1 = <->

proc id2{r} : ({r})()({r+1})1 |- ()({2*r})()1
proc id2{r} = <->

proc id3 : 1 |- ({0})1
proc id3 = <->

(*
proc id4 : 1 |- ({1})1
proc id4 = <->
*)
