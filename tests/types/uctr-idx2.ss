#options --syntax=explicit

type even{n} = &{inc : odd{n+1}}
type odd{n} = &{inc : even{n+1}}

proc zero : even{0}
proc zero = caseR (inc => zero || esucc{0})

proc esucc{n} : even{n} |- odd{n+1}
proc osucc{n} : odd{n} |- even{n+1}

proc esucc{n} = caseR (inc => esucc{n} || osucc{n+1})
proc osucc{n} = caseR (inc => osucc{n} || esucc{n+1})
