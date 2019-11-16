#test success
#options --work=none --time=none --syntax=implicit

type list = +{cons : list, nil : 1}

decl append : (l1 : list) (l2 : list) |- (l : list)

proc l <- append <- l1 l2 =
  case l1 ( cons => l.cons ; l <- append <- l1 l2
          | nil => wait l1 ; l <- l2 )
