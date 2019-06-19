#options --syntax=implicit
#test success

type nat{n} = +{z : ?{n <= 0}. 1, s : ?{n >= 1}. nat{n-1}}

proc succ{n} : nat{n} |- nat{n+1}

proc succ{n} = R.s ; <->