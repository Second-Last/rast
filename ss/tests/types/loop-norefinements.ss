#options --work=none --syntax=explicit
#test success

% looped during type-checking
% but no more

type even = +{s:+{s:even}}
type odd = +{s:+{s:odd}}

proc id : even |- +{s:odd}
proc id = <->
