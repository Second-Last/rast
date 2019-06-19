#options --work=none --syntax=explicit
% succeeds, because gcd(2,3) = 1

type even{n} = +{s:+{s:even{n}}}
type odd{n} = +{s:+{s:+{s:odd{n}}}}

proc id{n} : even{n} |- +{s:+{s:odd{n}}}
proc id{n} = <->
