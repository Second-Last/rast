#options --work=none --syntax=explicit
#test approx error

type ctr{n} = &{inc : !{10 > n*n}. ctr{n+1}}

proc Q{n} : ctr{n+1} |- ctr{n}

proc Q{n} = caseR (inc => assumeR {10 > n*n} ; <->)

proc Q5 : ctr{6} |- ctr{5}

proc Q5 = Q{5}

proc RR{n} : ctr{n} |- ctr{n+1}

proc RR{n} = L.inc ; assertL {10 > n*n} ;
             <->

proc R5 : ctr{5} |- ctr{6}

proc R5 = RR{5}

proc QR : ctr{6} |- ctr{6}

proc QR = Q5 || R5

exec QR