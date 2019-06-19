#options --time=recv --work=none --syntax=implicit
#test success

proc sub1 : 1 |- 1
proc sub1 = <->

proc sub2 : ()1 |- ()1
proc sub2 = <->

proc sub3 : []1 |- ()1
proc sub3 = <->

proc sub4 : ()1 |- <>1
proc sub4 = <->

proc sub5 : []1 |- []1
proc sub5 = <->

proc sub6 : <>1 |- <>1
proc sub6 = <->

proc sub7 : ()[]1 |- []()1
proc sub7 = <->

proc sub8 : <>()1 |- ()<>1
proc sub8 = <->

proc sub9 : []1 |- <>1
proc sub9 = <->
