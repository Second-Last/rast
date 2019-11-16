#test success
#options --work=none --time=none --syntax=implicit

type nat = +{zero : 1, succ : nat}

type list = +{cons : nat * list, nil : 1}

decl append : (l1 : list) (l2 : list) |- (l : list)

proc l <- append <- l1 l2 =
  case l1 ( cons => l.cons ;
                    n <- recv l1 ; send l n ;
                    l <- append <- l1 l2
          | nil => wait l1 ; l <- l2 )
