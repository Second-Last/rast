#test success
#options --work=send --syntax=explicit

type listA1 = +{cons : |{2}> A * listA1, nil : 1}
type listA0 = +{cons : A * listA0, nil : 1}

decl append : (l1 : listA1) (l2 : listA0) |- (l : listA0)

proc l <- append <- l1 l2 =
  case l1 (
    cons => get l1 {2} ; x <- recv l1 ; l.cons ; send l x ; l <- append <- l1 l2
  | nil => wait l1 ; l <- l2
  )