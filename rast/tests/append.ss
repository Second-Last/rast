#test success
#options --work=send --syntax=explicit

type list1 = +{cons : |{1}> list1, nil : 1}
type list0 = +{cons : list0, nil : 1}

decl append : (l1 : list1) (l2 : list0) |- (l : list0)

proc l <- append l1 l2 =
  case l1 (
    cons => get l1 {1} ; l.cons ; l <- append l1 l2
  | nil => wait l1 ; l <-> l2
  )