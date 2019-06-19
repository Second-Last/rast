#options --work=none --syntax=explicit
#test success

% looped during type-checking
% but not any more

type even{n} = +{s:+{s:even{n}}}
type odd{n} = +{s:+{s:odd{n}}}

proc id{n} : even{n} |- +{s:odd{n}}
proc id{n} = <->
