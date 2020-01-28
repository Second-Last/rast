#options --work=none --syntax=explicit

% this is like loop1 but creates intermediate
% definitions that prevent looping

type even{n} = +{s:even1{n}}
type even1{n} = +{s:even{n}}
type odd{n} = +{s:odd1{n}}
type odd1{n} = +{s:odd{n}}

proc id{n} : even{n} |- +{s:odd{n}}
proc id{n} = <->
