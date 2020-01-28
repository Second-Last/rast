#options --syntax=explicit
#test success

type unit{n} = 1
eqtype unit{n} = unit{m}

proc done : unit{0}
proc done = closeR
exec done
