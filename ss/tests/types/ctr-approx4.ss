#options --work=none --syntax=explicit
#test approx success

type ctr{n} = &{dec : !{n*n > 0}. ctr{n-1}}

proc P{n} : ctr{n} |- ctr{n+1}

proc P{n} = caseR (dec => assumeR {(n+1)*(n+1) > 0} ; <->)

proc P5 : ctr{5} |- ctr{6}

proc P5 = P{5}

proc RR{n} : ctr{n+1} |- ctr{n}

proc RR{n} = L.dec ; assertL {(n+1)*(n+1) > 0} ; <->

proc RR5 : ctr{6} |- ctr{5}

proc RR5 = RR{5}

proc PR5 : ctr{5} |- ctr{5}

proc PR5 = P{5} || RR{5}

exec PR5