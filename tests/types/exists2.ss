#options --time=recv --syntax=implicit
#test error

proc simple : ?{0 = 0}. 1 |- ()?{0 = 0}. 1

proc simple = <->
