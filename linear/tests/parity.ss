#test success
#options --time=recvsend --syntax=explicit

type bool = +{b0 : `1, b1 : `1}
type tree{h} = &{parity : `({5*h+2}) bool}

decl xor : (a : bool) (b : ()() bool) |- (c : ()()()() bool)
decl leaf : . |- (t : tree{0})
decl node{h} : (l : () tree{h}) (r : ({3}) tree{h}) |- (t : tree{h+1})

proc t <- leaf <- =
  case t (
    parity => delay {2} ;
              t.b0 ;
              close t
  )

proc t <- node{h} <- l r =
  case t (
    parity => l.parity ;
              delay ;
              r.parity ;
              delay {5*h} ;
              t <- xor <- l r
  )