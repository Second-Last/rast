#options --work=none --syntax=explicit
#test approx success

type ctr{n} = &{dec : !{n*n > 5}. ctr{n-1}}

proc Q{n} : ctr{n} |- ctr{n+1}

proc Q{n} = caseR (dec => impossibleR {(n+1)*(n+1) > 5})

proc Q5 : ctr{5} |- ctr{6}

proc Q5 = Q{5}

exec Q5