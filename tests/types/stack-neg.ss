#options --time=recvsend --syntax=implicit
#test error

type stack = &{push : `&{b0 : `[]stack, b1 : `[]stack},
               pop : `+{none : `1, some : `+{b0 : `[]stack, b1 : `[]stack}}}


proc client{n} : []stack |- ({2*n})1

proc client{n} = L.push ; L.b0 ; client{n-1}