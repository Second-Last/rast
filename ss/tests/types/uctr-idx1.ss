#options --syntax=explicit

type uctr{n} = &{inc : uctr{n+1}}

proc zero : uctr{0}
proc zero = caseR (inc => zero || succ{0})

proc succ{n} : uctr{n} |- uctr{n+1}
proc succ{n} = caseR (inc => succ{n} || succ{n+1})
