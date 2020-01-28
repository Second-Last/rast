#options --syntax=explicit
#test success

type ctr{n} = &{inc : ctr{n+1}}

proc zero{k} : ctr{k}

proc zero{m} = caseR ( inc => zero{m+1} )