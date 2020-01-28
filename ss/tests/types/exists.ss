#options --time=recv --work=none --syntax=implicit
#test success

proc simple : ?{0 = 0}. 1 |- ()?{0 = 0}. 1

proc simple = waitL ; closeR