#options --time=none --work=none --syntax=explicit
#test error

proc id : 1 |- 1

proc bogus : 1 |- 1
proc bogus = id

exec bogus
