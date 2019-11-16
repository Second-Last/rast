#test success
#options --syntax=explicit --time=recvsend

type A = [] 1
type streamA{k} = A * `({k}) streamA{k}

decl alternate{k} : (l1 : streamA{2*k+3}) (l2 : ({k+2}) streamA{2*k+3}) |- (l : () streamA{k+1})

proc l <- alternate{k} <- l1 l2 =
  x <- recv l1 ;
  send l x ;
  delay {k} ;
  l <- alternate{k} <- l2 l1