#options --syntax=explicit
#test error

type ctr{n} = &{inc : ctr{n+1}}

proc zero : ctr{0}

proc zero = caseR ( inc => zero )